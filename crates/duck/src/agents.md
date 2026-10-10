# Duck

Indentation-blocked, statically typed, compiled to one WebAssembly component.
Values live in wasm locals and globals, memory is raw pointers into linear
memory, and the host supplies all I/O through `extern`. `duck build` compiles
the package of the nearest `Duck.toml` to a component of the world it names,
and `duck run` runs it with WASI. `duck format` lays its files out as the
examples here are.

Absent: allocator, GC, standard library, closures, anonymous functions,
methods, traits, overloading, varargs, ternary, ranges, exceptions, char type,
string operations.

## Syntax

```duck
extern:                          # host functions, which the world imports
	fn log(n: i32)

pub let LIMIT = 100              # immutable global
var count: i32 = 0               # mutable global

pub struct Point:                # items and fields are private unless `pub`
	pub x: f32
	pub y: f32 = 0.0             # a default: a constructor may leave `y` out

enum(u8) Color:
	red                          # 0
	green = 5
	blue                         # 6

fn area(w: f64, h: f64 = 1.0) -> f64:   # a default: a call may leave `h` out
	return w * h

pub fn main():                   # no `->`: returns `tuple()`, the unit type
	let a = area(2.0, h: 3.0)    # labels may reorder; positional ones first
	var p = Point(x: 1, y: 2)    # labelled: every field without a default
	p.x += a as f32              # also -= *= /= %=, and no others
	let (q, _) = (count / 3, p)
	if q > 10 and not p.x == p.y:
		log(q)
	else if q < 0:
		return
	else:
		pass                     # the empty block
	while true:
		count += 1
		if count == LIMIT:
			break
	for c in Color:              # each member; or each element of an array
		log(c as u8 as i32)
```

- A statement ends with its line. Lines break freely inside `()` and `[]`.
- Items are declared in any order. `let` bindings and parameters are
  immutable, and shadowing is allowed. Conditions are `bool`.
- A parameter anywhere in the list may have a default. Label a later argument
  to skip one: with `fn f(a: i32, b: i32 = 1, c: i32 = 2)`, `f(0, c: 5)`.
- Keywords: `pub fn let var return if else while for in break continue pass
  defer match struct enum union extern use module and or not true false as
  as!`. No item is named `array`, `varray`, `string`, `tuple`, `type`,
  `option`, `result` or `never`.

## Types

- `i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 bool`. Integer arithmetic wraps.
  Numeric types never mix (`u8 + i32` is an error): convert with `as`.
- `int` and `uint`: integers as wide as an address, which is 32 bits. They
  count bytes and elements, and are types of their own: `uint + u32` is an
  error too.
- `tuple(A, B)`: built `(a, b)`, read `t.0`. Unit is `tuple()`, written `()`.
- `&T` reads its pointee and `&var T` also writes it. Both are unchecked
  addresses, which `as!` makes of any address. There is no null: `0` is an
  address like any other.
- `option(T)`: the union of `none` and `some: T`. `result(T, E)`: the union
  of `ok: T` and `err: E`. Both are built in, and are unions in every way.
- `array(T)`: a view of `ptr: &T` and `len: uint` that owns nothing.
  `varray(T)` has a `ptr: &var T`, so its elements are assignable.
- `string`: an alias of `array(u8)`, which holds UTF-8. It is built as an
  array is: `string(ptr: p, len: n)`.
- `fn(A, B) -> R`: a function pointer. `fn(A)` returns nothing.
- A type has a `size: uint` and an `align: uint`, as in `Point.size`,
  `(&Point).size` and `i64.align`. It is no value: `type` is only the type of
  a function's parameter, which makes it a type parameter.
- `externref`: an opaque host reference. It is never stored in memory or
  compared.
- `never`: the type of what has no value, as a `return` has none. It is
  accepted as any type, and nothing else is accepted as it, so no value of
  it is made: a function that returns it never returns. It is never stored
  in memory, so it has no `size`, and is no type argument of a function.
- `Name`, `Name(T)`, `mod.Name`: structs, unions and enums, passed by value
  like tuples and arrays.
- A struct or union holds itself only behind a pointer, whatever its type
  arguments, and holds others by value at most 64 deep.
- `enum(T) Name:` makes each member a constant of any type `T`. Integer
  members count up from the one before, and other types need every value.
  Enums support `Name.member`, `==`, `!=`, `e as T` and `for m in Name`.
  Nothing converts a `T` to the enum.

A `&var T` is accepted as a `&T`, and a `varray(T)` as an `array(T)`, for the
type as a whole only: a `tuple(&var T, i32)` is not a `tuple(&T, i32)`, and a
`fn(&T)` is not a `fn(&var T)`. No other type is accepted as another, whatever
the two hold: only a `use` relates them, which a bound and `as` ask.

## Unions

```duck
union Shape:
	circle: f32                  # a variant holds one value
	rect: tuple(f32, f32)
	empty                        # or none

union(A, B) Either:              # generic, as a struct is
	left: A
	right: B

enum(u8) Fault:
	empty
	huge

fn area(s: Shape) -> result(f32, Fault):  # built in, as `option(T)` is
	let unit = Shape.rect((1.0, 1.0))  # one argument: a tuple is not spread
	if s == unit:
		return result(f32, Fault).ok(1.0)
	if s == .empty:                    # `.name`: the type expected has it
		return .err(.empty)            # an enum's member too
	return .err(.huge)
```

- A value holds one variant. `Shape.circle(1.0)` builds one that holds a
  value and `Shape.empty` one that doesn't. A generic union takes its type
  arguments, as in `result(f32, Fault).ok(1.0)`.
- `.name` and `.name(value)` are the variant, or the enum member, of the type
  expected there: by a `return`, an annotated binding, an assignment, an
  argument, the value of a field or variant, or the other side of an
  operator. `let x = .empty` is an error. So is `.name` where a type
  parameter `T` is expected, as a `T` has no variants or members.
- `==` and `!=` compare which variant each holds and then its value. Only
  `match` reads that value: a union has no fields.
- A union has 1 to 256 variants, which are as `pub` as it is. A variant
  named `size` or `align` hides that of the type.
- In memory a union is a `u8` that counts its variants from 0 and then the
  largest variant, at the largest alignment, as C lays out
  `struct { uint8_t tag; union { ... }; }`.

## Match

```duck
union Shape:
	circle: f32
	rect: tuple(f32, f32)
	empty

enum(u8) Color:
	red
	green

fn area(s: Shape) -> f32:
	match s:                     # evaluated once
		.circle(r):              # `r` is the `f32` the variant holds
			return r * r
		.rect((w, _)):           # in a pattern that `let` takes
			return w
		.empty:
			return 0.0

fn code(c: Color, s: Shape) -> i32:
	match c:
		.red:                    # an enum's member
			return 1
		else:                    # every other value: the last arm
			pass
	match s:
		.empty:
			return 2
		other:                   # a name matches every value, and is it
			return 3

fn word(s: array(u8), strict: bool) -> i32:
	match (s, strict):           # patterns nest
		("zero", _):             # a string, compared whole
			return 0
		([first, _], true):      # an array of exactly two elements
			return first as i32
		([], false):
			return -1
		else:
			return 1
```

- The first arm whose pattern matches runs, and no other. `break` and
  `continue` in an arm act on the loop around the `match`.
- A pattern is one of these, and those within it are too:
  - a name, which matches every value, or `_`, which also does
  - `.name` or `.name(pattern)`: a variant of the value's union and what it
    holds, or `.name`, a member of its enum
  - `(a, b)`: a tuple, by its elements
  - `[a, b]`: an array of exactly as many elements, by each
  - a number, which may be negative, `true`, `false`, or a string for an
    `array(u8)`: the value that `==` finds equal
- A pattern never names a type or a constant: `Shape.empty:` is an error,
  and `LIMIT:` is a new name. Structs, pointers and function pointers match
  names and `_` only.
- A name is an immutable copy of what it matches. Match memory through
  `match p.*`, and change it by writing a whole value: `p.* = .circle(1.0)`.
- The arms match every value of the type between them, or the `match` is an
  error that names what is left out. Numbers, arrays and strings have no end
  of values, so they need a name, `_` or `else`. An arm that those before it
  leave nothing for is an error too, as an `else` after every variant is.
- A value that no arm matches traps: memory cast to a union or enum can hold
  one, as can a value from the host.
- In a generic body a value of type `T` matches a name, `_` or `else` only.
- `let` and `var` take names, `_` and tuples, which can't fail to match.

## Literals and globals

**String and array literals belong in global initializers and defaults only.**
In a function, name a global. Only a string that is a pattern of a `match` is
written in one.

```duck
let greeting = "hello"             # array(u8)
let primes: array(u16) = [2, 3, 5]
let empty: array(i32) = []         # [] needs an annotation
let SIZE: uint = 1024
let buf: varray(u8) = [0; SIZE]    # writable; zeros add nothing to the wasm
let count = &var 0                 # &var i32: one writable value in memory

fn f(i: uint) -> u8:
	buf[i] = greeting[i]           # a uint index, bounds checked
	count.* += 1
	return buf[0]
```

- A literal is a read-only `array` unless its global is annotated `varray`.
- In an initializer, `&value` and `&var value` place a value in memory, as
  a literal is, and give its address: `&var State()`, `&Mode.idle`. A name is
  copied, so `&N` twice is two addresses.
- An integer literal takes the type expected of it, which may be a float or a
  pointer (`let p: &u8 = 16`), and is otherwise `i32`. A float literal is
  `f64` by default and has a digit on each side of the `.`.
- A `varray` literal in a field default is empty and it has no `&var value`,
  as every value would share the memory. A parameter default has the same
  rule, and never uses another parameter: `end: uint = a.len` is an error.
- Only a constructor applies field defaults. Memory that is cast to a struct
  holds whatever was there.

## Constants

A global initializer, an enum member's value and a default are constants:
each is any expression, evaluated once, while the program is compiled. One
that calls a function runs it then.

```duck
let squares: varray(u32) = [0; 256]
var ids = 0

fn fill() -> uint:
	var n: uint = 0
	while n < squares.len:
		squares[n] = (n * n) as u32  # in the memory the module starts with
		n += 1
	return n

fn id() -> i32:
	ids += 1                         # the module starts with `ids` as 3
	return ids

let filled = fill()                  # run while compiling
let first = id()                     # 1
let second = id()                    # 2: a file runs top to bottom
pub let largest = squares[filled - 1]  # 65025, read from memory

enum(u32) Limit:
	low = squares[4]                 # 16
	high = squares[8]

fn area(w: i32, h: i32 = id()) -> i32:  # 3, for every call without an `h`
	return w * h
```

- The module starts as its constants left it: with every byte they wrote,
  anywhere in memory, with the pages they grew it to, and with each `var` as
  they last assigned it. Nothing separates the two: a function runs the same
  for a constant as for the host. Zero what was only scratch, as every other
  byte is in the wasm.
- Constants run in order: those of a module that is used before those of the
  module that uses it, and each file top to bottom. One that another reads
  runs first, wherever it is declared, as does one that a function the other
  may call reads. Each runs once. `let _ = init()` runs `init` for what it
  does alone.
- The length of `[value; len]` runs before the rest of its initializer does.
- No constant is used in its own definition: a global in its initializer, an
  enum in its members' values, a struct's defaults in that struct's
  defaults, or a function's in that function's. Nor may the functions it
  calls or takes pointers to read it, or those they call, whether or not
  they would when it runs.
- A constant calls no `extern` function: the host isn't there yet. That, a
  trap and running out of fuel are each an error where the constant is, which
  names the functions that were running. Nothing runs after an error.
- A default is one value, made once: `h: i32 = id()` calls `id` once, not
  once for each call that leaves `h` out.
- A constant has no `return`: it is evaluated for no function.
- The constants of one item share its fuel, which `[const]` in `Duck.toml`
  sets, and is about a second's worth without it.
- A constant takes memory as the host's code does, with `module.grow`, and
  the module starts with what it took. A literal is never placed in a page
  that `grow` gave.

## Operators

Loosest to tightest, the binary ones left associative but for assignment,
which is right associative: `return`, `= += -= *= /= %=`, `|>`, `or`, `and`,
`not`, `== != < <= > >=`, `|`, `^`, `&`, `<< >>`, `+ -`, `* / %`, `as as!`,
prefix `- ~ & &var`, postfix `f(x) a[i] x.f t.0 p.*`.

```duck
fn half(n: i32) -> i32:
	n >= 0 or return -1          # returns only where `n` is negative
	n % 2 == 0 and return n / 2
	return (n + 1) / 2

fn log2(n: u32) -> u32:
	var bits: u32 = 0
	while true:
		n >> bits > 1 or break   # leaves the loop
		bits += 1
	return bits
```

- A `return` is an expression, written wherever an operand is. Its value is
  all that follows it: `ok or return a or b` returns `a or b`. It has none
  where nothing that starts an expression follows, as in `f(return)`.
- It has no value of its own, as it leaves the function: its type is `never`,
  which is accepted as any type. What is made of a `never` is one too, so
  `f(return 1)` and `let x = return 1` are accepted, and return 1.
- A `break` and a `continue` are expressions as a `return` is, with no value
  to take, and each is a `never`. One in the condition of a `while` is of
  that loop: `while more() or break:`.
- A function with a result ends in a `never` wherever it ends: a `return`,
  `module.unreachable()` or a call of a function that returns `never`, in a
  statement that always evaluates it. The right side of `and` and `or` may
  not be evaluated, so a `return` there ends nothing: `half` needs its last
  line.

```duck
extern:
	fn exit(code: i32) -> never  # the host never returns from it

fn fail(code: i32) -> never:     # nor does this: it ends in a `never`
	exit(code)

fn positive(n: i32) -> i32:
	if n > 0:
		return n
	fail(1)                      # ends the function, as a `return` does
```

- A function that returns `never` has no `return` but of a `never`, and
  must end in one. A call of one traps if it does return, as a host
  function may.

- An assignment is an expression: its value is the one assigned, as the
  target's type. So `a = b = 0` assigns both, and `while (n = next()) != 0:`
  tests what it read. Its target is a variable, a field, `a[i]` or `p.*`.
- The target is found first, then the value is evaluated, then it is stored.
  Operands are evaluated left to right, each as its variables were then:
  `x + (x = 5)` adds what `x` was to 5.
- `%` and `~` take integers, and unary `-` takes signed integers and floats.
  Integer division by zero traps.
- `==` and `!=` compare any one type structurally, arrays by length and
  elements. `< <= > >=` compare numbers and pointers.
- `as` makes a value one of another type that it is, or is near enough:
  number to number (float to integer saturates, NaN gives 0, and a narrower
  one may lose precision), `bool` to integer, an enum to its value type, a
  union or an enum to a wider one, which starts as it does, and a struct to
  one that it starts as, which is its first fields, or to the array that it
  starts as. Only a `use` makes one type start as another, not what the two
  hold. Nothing converts to `bool`: write `x != 0`.
- Of addresses, `as` makes a pointer or a function pointer an `int` or a
  `uint`, a `&var T` a `&T`, a `varray(T)` an `array(T)`, and a pointer to a
  struct one to a struct or an array that it starts as: a `&Named` a `&Head`,
  and a `&var Named` a `&var Head`. A `&varray(T)` is a `&array(T)` so too.
- A pointer that writes is one only to what is typed just as its pointee is:
  a `&var Vec(T)` that starts as a `varray(T)` is a `&var varray(T)` and a
  `&array(T)`, and no `&var array(T)`, as a `&var varray(T)` is none. What
  was stored through it would be written through.
- `as!` makes an address one of any type, and checks nothing: pointer to
  pointer (how a `&T` becomes a `&var T`, and a `&Head` a `&Named`), `int`
  or `uint` to a pointer or a function pointer, function pointer to function
  pointer, and `array(T)` to `varray(T)`. What is at the address is read as
  the type says, whatever is there.
- `as!` also makes an integer the float that has its bits, and a float the
  integer: an `i32` or a `u32` and an `f32`, an `i64` or a `u64` and an
  `f64`. `1 as f32` is `1.0`, and `0x3f800000 as! f32` is too. It casts no
  other value: `x as! u8` and `p as! uint` are errors, as is `as` where
  only `as!` casts.
- No other integer converts to or from a pointer: go through `uint`, as in
  `p as uint as u32`.

## Pointers and memory

```duck
struct Node:
	val: i32
	next: &Node

var heap: uint = 0                     # the next free byte
var end: uint = 0                      # where the page that holds it ends

fn alloc(T: type) -> &var T:           # bump through pages that `grow` gives
	heap = (heap + T.align - 1) / T.align * T.align
	if heap + T.size > end:
		heap = module.grow(1) as uint * module.page_size
		end = heap + module.page_size
	heap += T.size
	return (heap - T.size) as! &var T

fn push(head: &Node, v: i32) -> &Node:
	let n = alloc(Node)                # a `&var Node`
	n.* = Node(val: v, next: head)     # `p.*` is the whole pointee
	n.val += 1                         # fields auto-dereference
	let r: &var i32 = &var n.val       # `&place` gives a `&T`
	r.* = 0
	return n

fn view(p: &i32, len: uint) -> array(i32):
	return array(i32)(ptr: p, len: len) # slice by building a new view
```

- `&` and `&var` take the address of `p.field`, `p.*` and `a[i]` only. Locals,
  parameters and globals have no address: only a global initializer or
  default gives a value one, by placing it.
- A write needs a `var` local, a `&var` or a `varray`, and only the last
  pointer or array on the way to the place decides: with `next: &var Node`,
  `p.next.val = 1` works through a `p: &Node`. `let` and `var` govern the
  binding, not the pointee.
- `a[i]` reaches its array through any number of pointers, as `p.field` does
  its struct: with `p: &varray(u8)`, `p[0] = 1`. `for` takes the array
  itself: `for x in p.*`.
- Pointer arithmetic is `((p as uint) + 4) as! &T`.
- Layout follows C, and `bool` is 1 byte. A pointer, a function pointer, an
  `int` and a `uint` are each 4 bytes.
- The only runtime checks are array bounds and division by zero, which trap.
- Literals are placed from address 0, or from `static.start` in `Duck.toml`.
  Memory starts as the fewest pages that hold them, which is none without
  literals, and those its constants grew it by.
- A page is yours only if `module.grow` gave it: its result is the first of
  the new pages. Never pick an address past the literals, as nothing says
  where they end. Literals keep to this while the program is compiled: one
  that the page of the last has no room for goes in the pages after it, or
  past every page that a constant has grown memory by since.

`module` is built in. Its functions are single wasm instructions and have no
pointers.

- `module.page_size` and `module.max`: `uint` constants for the bytes in a
  page and the pages memory may grow to.
- `module.size() -> uint` and `module.grow(pages: uint) -> int` count pages.
  `grow` gives the old size, or -1.
- `module.memory() -> varray(u8)` is all of memory from address 0.
- `module.fill(dst: &var u8, value: u8, len: uint)` and
  `module.copy(dst: &var u8, src: &u8, len: uint)`. `copy` handles overlap.
- `module.unreachable()` traps. It is a `never`, as a `return` is, and ends
  a function as one does: `ok or module.unreachable()`.
- `module.count_leading_zeros(x)` and `module.count_trailing_zeros(x)` take
  any integer type and give that type.

## Defer

```duck
extern:
	fn open() -> i32
	fn read(file: i32) -> i32
	fn close(file: i32)
	fn log(n: i32)

var heap: uint = 0

fn sum() -> i32:
	let mark = heap
	defer heap = mark                # as `sum` is left, by either `return`
	let file = open()
	defer close(file)                # before that: the last `defer` runs first
	var total = 0
	while true:
		let n = read(file)
		defer:                       # a block, run as each iteration ends
			log(n)
			log(total)
		if n < 0:
			return total             # `total`, and then all three
		if n == 0:
			break                    # only that of the loop's body
		total += n
	return -1
```

- `defer` takes one expression on its line, or `defer:` and a block. Nothing
  runs where it is written. Its body runs when the block that the `defer` is
  in is left: at its end, or by a `return`, `break` or `continue`.
- The block is the nearest: the body of a function, an `if`, an `else`, a
  loop, an arm or another `defer`. One in a loop's body runs as each
  iteration ends, and one in an `if` as the `if` ends, not the function.
- The defers of a block run last first, and those of a block before those of
  the block around it. Only those that were reached run: a `return` above a
  `defer` doesn't run it.
- The body names what is in scope where it is written, and reads each
  variable as it is when it runs: `defer log(n)` logs what `n` is by then.
- `return value` evaluates `value`, then runs the defers, then returns it.
  No defer changes what is returned: `return n` with `defer n = 0` returns
  what `n` was.
- A body has no `return`, and no `break` or `continue` of a loop that the
  `defer` is in. A loop within the body has its own. A `defer` within it
  runs as the body ends.
- A statement that is no `defer` follows a `defer` in its block. One that
  only others follow would run where it is written, so it is an error: write
  its statement alone, or `pass` after it.
- A `defer` ends no function: one with results still needs its `return`,
  whatever the body is.
- **A trap runs no defer.** `module.unreachable()`, an index out of bounds
  and a division by zero end the program where they are, as does a host
  function that never returns, like the `exit` of `wasi:cli/exit`.

## Generics

```duck
struct(T) Box:
	value: T

struct Head:                         # used as a bound below
	id: i32

struct Named:
	use Head                         # `id: i32`, so it starts as `Head` does
	name: array(u8)

let nobody = &Named(id: 0, name: "")

var heap: uint = 0

fn new(T: type) -> &var T:           # a call gives `T` a type: new(Named)
	if heap == 0:
		heap = module.grow(1) as uint * module.page_size  # one page, taken once
	heap += T.size
	return (heap - T.size) as! &var T

fn(T) boxed(value: T) -> &var Box(T):  # a call infers `T` from `value`
	let b = new(Box(T))
	b.value = value
	return b

fn(T: Head) id(x: &T = nobody) -> i32:   # `T` is a struct that starts as `Head` does
	return x.id

fn(T, B: Box(T)) unbox(b: &B) -> T:  # a bound names the type parameters before it
	return b.value

fn demo(n: &Named) -> i32:
	let b = boxed(n.id)              # `T` is `i32`
	let c = Box(u8)(value: 1)        # generic structs always take type arguments
	let v = unbox(b)                 # `B` is `Box(i32)`, so `T` is `i32`
	return id(n) + id() + v          # `id()` is of the default, so `T` is `Named`
```

- A type parameter is a type of which only the size and alignment are known.
  A `T` is bound, passed and returned, read and written through a `&var T`,
  and held by other types: `&T`, `array(T)`, `Box(T)`. A pointer to one is
  cast as any pointer is, with `as!`. `T.size` and `T.align` are those of
  the type.
- A `T` has no operators, literals, fields, constructor or members: `a > b`,
  `a == b`, `0 as T`, `T(x: 1)` and `T.ok` are errors where they are written,
  whatever the function is called with. So a generic body is checked once,
  as declared, and is right for every type argument.
- `fn(T) f(x: T)`: each call infers `T` from its arguments, so `T` is in the
  type of a parameter, or in the bound of a type parameter that is.
- `fn f(T: type)`: each call gives `T` a type as that argument, `f(u8)` or
  `f(T: u8)`. `T` is a type throughout the signature and the body. It has no
  default, and is nothing at run time. A function may have both kinds.
- `fn(T: Head)`, `struct(T: Head)`: `T` is bounded by the struct `Head`, so a
  type argument is a struct that starts as `Head` does: `Head` itself, a
  struct whose first `use` names it, or one whose first `use` names a struct
  that starts as it does. Its first fields are then those of `Head`, as they
  are there. A struct that only has fields named and typed as those of
  `Head` is not one, and nor is one that holds a `Head` as its first field.
- `fn(T: (Head, Meta))`: `T` is bounded by a list of the types that a type
  argument uses, first and in order: see below. `(Head)` is `Head`, and `()`
  bounds nothing.
- A bound may name the type parameters before its own in
  the list, and any that are parameters: `fn(T, B: Box(T))`. A type argument
  for `B` then starts as a `Box(T)` does, and a call that settles `B` takes
  `T` from it: with a `B` that starts with `use Box(f64)`, `T` is `f64`. A
  type argument is the bound's own: a `Box(&var u8)` is no `Box(&u8)`.
- In the body a `T` has the fields of `Head`, read and written as a struct's
  are, and is otherwise as any `T` is.
- `pub` plays no part in a bound. The body sees the fields that it sees in
  `Head`, and reads them of a type argument whose own are private.
- Only a type parameter is bounded. A function that takes a `Head` doesn't
  take a `Named`, and a `&Named` is not a `&Head`: cast it, `n as &Head`, or
  `n.* as Head` for the value. A `T` bounded by `Head` casts as `Head` does.
- A type argument is storable: nothing is generic over `externref`.
- A default, of a parameter or a field, is one value for every call and
  constructor, so it never names `T`, and is no value laid out by one:
  `none: option(T) = .none` is an error. It may fit the type as declared,
  like `p: &T = 0` and `items: varray(T) = []`, and then it infers nothing.
  Or it has a type of its own that the declared type stands for, like the
  `&Named` of `nobody` for a `&T`, which meets the bound of `T`.
- A call that leaves such an argument out takes `T` from the default's type,
  where no argument gives `T` another. A call or constructor that gives `T`
  another type has no default there: `Slot(u8)()` is an error where
  `struct(T) Slot` has `value: T = 7`, an `i32`, and `Slot(i32)()` is not.
- `p: &T` takes a `&var i32` with `T` as `i32`, and `array(T)` a `varray(i32)`.
  Nothing is generic over writability: write both, or cast.

### Wider unions and enums

```duck
union ReadError:
	closed
	timeout: u32

union IoError:
	use ReadError                    # starts as `ReadError` does, so is wider
	denied

enum(u8) Warm:
	red
	green = 5

enum(u8) Color:
	use Warm                         # `red` and `green = 5`
	blue

fn(E: IoError) code(e: E) -> i32:    # `E` is a union that `IoError` is wider than
	match e:                         # as an `IoError`
		.closed:
			return 1
		.timeout(ms):
			return ms as i32
		.denied:
			return 3

fn demo(r: ReadError, w: Warm) -> i32:
	let io = r as IoError            # the same variant, of the wider union
	let c = w as Color
	return code(r) + code(io) + c as u8 as i32
```

- A union is wider than one that it starts as: the union that its first
  `use` names, and any that one starts as. Its first variants are then those
  of the other. An enum is wider than the enum that its first `use` names so
  too, whose members are its own first ones, with the same values. Each is
  as wide as itself.
- Nothing else makes one wider: not a later `use`, and not variants or
  members that are named, typed and valued as another's are.
- `x as Wider` is the same variant or member of the wider type. Nothing
  converts the other way: `match` the wider one. The two unions aren't laid
  out alike, so a `&ReadError` is no `&IoError`, and only `as!` makes it or
  a `&Warm` the pointer to the wider type.
- A type parameter bounded by a union or an enum takes the types it is wider
  than, the reverse of a struct, which bounds those that start as it does. In
  the body a `T` is matched as the bound, with an arm for each of the bound's
  variants or members, and `x as IoError` is the bound's own value. It
  builds no `T`: `T.closed` and `.closed` for a `T` are errors, as a type
  argument may have no such variant.

## Use in a struct, union or enum

```duck
struct Head:
	pub id: i32
	tag: u8 = 7

struct Named:
	use Head                         # `pub id: i32` and `tag: u8 = 7`
	name: array(u8)

union ReadError:
	closed
	timeout: u32

union IoError:
	use ReadError                    # `closed` and `timeout: u32`
	denied

enum(u8) Warm:
	red
	green = 5

enum(u8) Color:
	use Warm                         # `red` is 0, and `green` is 5
	blue                             # 6

struct(T) Box:
	value: T

struct(T) Pair:
	use Box(T)                       # `value: T`
	other: T

let nobody = Named(id: 0, name: "")  # `tag` is 7

fn demo(n: &Named, r: ReadError) -> i32:
	let h = n as &Head               # `Named` starts as `Head` does
	let head = nobody as Head        # its first fields, by value
	let io = r as IoError            # `IoError` is wider than `ReadError`
	return h.id + head.tag as i32 + Color.red as u8 as i32
```

- A `use Type` line of a struct, a union or an enum stands for the fields,
  variants or members of `Type`, in order, as if they were written there.
  A struct uses a struct, a union a union, and an enum an enum whose values
  have the type its own do. Every `use` line comes before the lines of the
  declaration's own.
- A struct uses an `array(T)` or a `varray(T)` too, for its `ptr` and `len`,
  which are `pub`: see below.
- The type is `Name`, `mod.Name` or a generic one with its type arguments,
  which may be the declaration's own type parameters. A union may use an
  `option(T)` or a `result(T, E)`. Nothing uses a type parameter: `use T` is
  an error.
- A `Named` holds no `Head`, and is laid out as its fields are. A struct
  starts as what its first `use` names, and as what that starts as, so `as`
  makes it one, and a pointer to it a `&Head`. A union or an enum is wider
  than what its first `use` names, and than what that is wider than, which
  `as` makes it. A later `use` gives neither.
- Only a `use` relates two types. A struct with `pub id: i32` and `tag: u8`
  of its own is no `Head`, a bound of `Head` doesn't take it, and no `as`
  casts it. The error says that it has the fields and doesn't `use` it
  first.
- A used field keeps its type, `pub` and default as declared. A `next: &Node`
  of `Node` is a `&Node` wherever it is used, and a default is a constant of
  the module that wrote it. A field that isn't `pub` is private to the
  module that uses it, and its type holds no private type of another.
- A used member keeps a value that it was given. One given none counts up
  from the member before it, as it does where it is declared.
- No name is given twice, by a `use` or a line of its own: it's an error at
  whichever comes later.
- A `use` never leads back to itself, as `use B` in `A` does when `B` has
  `use A`.

### Bounds that list what is used

```duck
struct Head:
	id: i32

struct Meta:
	flag: u8

struct Both:
	use Head
	use Meta
	more: i64

struct Deep:
	use Both                         # starts as `Both` does
	last: u8

fn(T: (Head, Meta)) flag(x: &T) -> i32:  # `T` uses `Head` and then `Meta`
	let h = x as &Head               # it starts as the first of them
	return h.id + x.flag as i32

fn demo(b: &Both, d: &Deep) -> i32:
	return flag(b) + flag(d)
```

- `fn(T: (Head, Meta))`: `T` is bounded by a list, so a type argument is a
  struct whose first `use` lines name `Head` and then `Meta`, or a struct
  that starts as one. What follows them is its own.
- The order is the list's: a bound says how a type argument is laid out,
  and one with `use Meta` and then `use Head` has its fields elsewhere. In
  the body a `T` has the fields of each type, where a struct that uses only
  those has them. They are laid out one after another, as a struct's are,
  and not as a `tuple(Head, Meta)` is: nothing points to the `Meta` in one.
- Each type is the one that is used, and no other that starts as it: a
  struct with `use Named` and `use Meta` is no `(Head, Meta)`, though a
  `Named` starts as a `Head` does. Nor is one that uses a struct which has
  only `use Head` in it. An `array(T)` in a list takes a `varray(T)`.
- A list names structs and arrays, none of them twice, and no field of
  theirs twice: `(Head, Head)` is an error, as no struct uses both. Only a
  bound is a list, which no value has the type of.
- A `T` bounded by a list is cast, indexed and iterated as the first type in
  it is, and meets the bounds that it does.

### Structs that start as an array

```duck
struct(T) Vec:
	use varray(T)                    # `pub ptr: &var T` and `pub len: uint`
	cap: uint

let numbers: varray(i32) = [0; 8]
let vec = &var Vec(i32)(ptr: numbers.ptr, len: 0, cap: numbers.len)

fn(T) push(v: &var Vec(T), x: T):
	if v.len == v.cap:
		module.unreachable()
	v.len += 1
	v[v.len - 1] = x                 # through the pointer, as `v.len` is

fn(T, A: array(T)) last(a: A) -> T:  # an array, or a struct that starts as one
	return a[a.len - 1]

fn sum(a: array(i32)) -> i32:
	var total = 0
	for x in a:
		total += x
	return total

fn demo() -> i32:
	push(vec, 3)
	push(vec, 4)
	var total = sum(vec.* as array(i32))
	for x in vec.*:                  # each of its `len` elements
		total += x
	return total + last(vec.*) + last(numbers)
```

- A struct starts as an array when its first `use` names one, or names a
  struct that starts as one. One that starts as a `varray(T)` starts as an
  `array(T)` too. Fields of its own named `ptr` and `len` don't make it one.
- It is indexed and iterated as that array is: `v[i]` checks `i` against its
  `len`, and `for x in v` reads its `ptr` and `len` once, before the first
  iteration. An element is written only through a `varray(T)`.
- `as` makes it the array, `v as array(T)`, and a pointer to it one to the
  array, `p as &array(T)`: a `&var varray(T)` only of one that starts as a
  `varray(T)`, and never a `&var array(T)`. `as!` makes one that only reads
  a `varray(T)`.
  Nothing makes an array the struct, and a function that takes an `array(T)`
  doesn't take a `Vec(T)`: cast it.
- `fn(T, A: array(T))`: `A` is bounded by an array, so a type argument is an
  `array(T)`, a `varray(T)` or a struct that starts as either. A bound of
  `varray(T)` takes those that write. A call that settles `A` takes `T` from
  it.
- Nothing checks what is written through a bound that only reads: with a
  `p: &var A`, `p.ptr = s.ptr` leaves the `ptr` of an `array(T)` where the
  type argument has that of a `varray(T)`.
- In the body an `A` has the `ptr` and `len` of its bound, and is indexed,
  iterated and cast as the bound is. It is otherwise as any `T` is: `a == b`
  and the pattern `[x, y]` are errors.
- Nothing else of an array is the struct's. `==` compares its fields, so two
  of them are equal when they have the same `ptr`, whatever is there. The
  patterns `[x, y]` and `"text"` match arrays only: `match v as array(u8)`.

## Function pointers

```duck
fn double(x: i32) -> i32:
	return x * 2

fn(T) id(x: T) -> T:
	return x

let steps: array(fn(i32) -> i32) = [double, id]

fn demo(f: fn(i32) -> i32) -> i32:
	let g = double                 # a function's name is its pointer
	let h: fn(u8) -> u8 = id       # a generic one needs the type expected of it
	return f(g(1)) + steps[0](2) + h(3) as i32
```

- A call through a pointer takes every argument, positionally. Defaults
  belong to the function's name: `double` with one would still be only a
  `fn(i32) -> i32`.
- `extern` functions have pointers too. Calling a zeroed pointer traps.

## Pipes

```duck
fn add(a: i32, b: i32) -> i32:
	return a + b

fn demo(n: i32) -> i32:
	return n * 2
		|> add(_, _) - 1           # `_` is the piped value, evaluated once
		|> _ / 2                   # a deeper line starting with `|>` continues

fn last(n: i32) -> i32:
	n * 2
		|> add(_, 1)
		|> return _                # a `return` ends the chain
```

- The body uses `_` at least once: `x |> f(_)`, never `x |> f`.
- Nothing is piped on from a `return`: `x |> return _ |> f(_)` is an error,
  as its value would be the rest of the chain. Brackets say which is meant:
  `x |> return (_ |> f(_))`.
- What is piped to a `return` is typed before the `return` is read, as it is
  for any body: `1 |> return _` returns an `i32`, and `.none |> return _` is
  an error.
- A `_` belongs to the nearest pipe: in `x |> f(_, y |> g(_))` the second is
  `y`.
- A piped literal is typed before the body is read: `1 as u8 |> byte(_)`.

## Modules

Every file is a module, named by its path from the directory of the package's
entry: beside `src/main.duck`, `src/util/strings.duck` is `util.strings`. A
directory is not itself a module.

```
use util.strings                 # the module: strings.split(...)
use geo.{Point, len as length}   # its items: Point(x: 1), length(p)
use json.Value                   # from the Duck.toml dependency `json`
pub use geo.Color                # also reachable as `this.Color`
```

- A path starts at the package's root, or with a dependency, wherever the
  file is. A name that is both a module and a dependency is an error.
- The module is the file furthest along the path. What follows names its
  `pub` items, or goes on through a module it makes `pub`.
- `use` binds the last name of the path, or the one `as` gives. `{}` groups
  nest, and a module's `use` lines come before every other item.
- A dependency's library is its only module in reach: `json.Value`, or
  `json.value.Value` once it has `pub use value`.
- A used module's `pub` items are reached as `mod.item`:
  `geo.Point(x: 1, y: 2)`, `geo.Color.red`. A `pub` item's signature uses
  only `pub` types.
- Another file constructs a struct only if every private field has a default,
  and never gives a private field a value.
- Files may use one another. A `use` never leads back to itself, as
  `pub use b.x` in `a` does when `b` has `pub use a.x`.

## Host

A component is one of a world, written in WIT, which says what its host gives
it and what it gives its host. `Duck.toml` names the world.

```wit
package my:pkg@0.1.0;

interface host {
    print-bytes: func(s: list<u8>);
    current-time: func() -> u64;
    poll: func() -> s32;
}

interface math {
    add: func(a: s32, b: s32) -> s32;
    negate-it: func(a: s32) -> s32;
}

world app {
    import host;
    import trace: func(code: u32);
    export math;
    export tick-now: func(dt: f64) -> f64;
}
```

```duck
extern "my:pkg/host@0.1.0":            # an interface the world imports
	fn print_bytes(s: array(u8))        # `print-bytes` there
	fn now() -> u64 = "current-time"    # the name the WIT has for it
	pub fn poll() -> i32                # callable from other files

extern:                                 # what the world itself imports
	fn trace(code: u32)

pub "my:pkg/math@0.1.0":                # an interface the world exports
	fn add(a: i32, b: i32) -> i32:
		return a + b
	pub fn negate(a: i32) -> i32 = "negate-it":  # callable from other files
		return 0 - a

pub fn tick_now(dt: f64) -> f64:        # `tick-now`, which the world exports
	trace(negate(1) as u32)
	return dt

pub fn helper():                        # only `pub`: the world has no `helper`
	pass
```

- An `extern "interface":` block declares functions of an interface the world
  imports, which is named in full, with its version, as the WIT names it. A
  block without a name declares functions the world itself imports. A block
  declares only the functions that are called.
- A `pub "interface":` block defines the functions of an interface the world
  exports. Only the entry file has one, each interface has one block, and the
  block defines every function of the interface. Its functions are otherwise
  as any of the file are: called by name, and private to it unless `pub`.
- A function the world itself exports is a `pub fn` of the entry file with
  its name, or one that a `pub use` there binds as it: `pub use geo.area`
  exports `area`. A `pub fn` the world doesn't export is only `pub`.
- Everything the world exports is defined, and the error names what isn't. A
  block of an interface the world doesn't export is an error, as is a
  function in one that the interface doesn't have.
- A function is named for the host as WIT names it, which is its own name
  with a `-` for each `_`: `print_bytes` is `print-bytes`. An `= "name"`
  after the signature gives another, before the `:` of a function with a
  body. One is needed where the name is none in WIT, whose names are words
  of lowercase letters or of capitals: `_x`, `a__b` and `getHttp` are errors
  in an `extern` block and in a `pub "interface":` block.
- A function of either block is checked against the WIT: it has as many
  parameters as the WIT gives it, each of the type that the WIT's is, and
  gives what the WIT has it give, or nothing. An `-> never` is for one that
  gives nothing and never returns.
- A type of Duck is one of WIT by its shape, whatever it and what it holds
  are named. A `record` is a struct with as many fields, each the type of
  the field it is in order, and a `variant` a union with as many variants,
  each holding what its case does. An `enum` is an `enum(u8)` with as many
  members, counted from 0, so none is given a value: an `enum(u16)` past
  256 of them. `flags` are the narrowest of `u8`, `u16` and `u32` with a
  bit for each, from the lowest. A `list<T>` is an `array(T)` and a
  `string` an `array(u8)`, which `string` names. `tuple`, `option` and
  `result` are Duck's own, with `tuple()` for a `_`. A `char` is a `u32`,
  `s8` to `s64` are `i8` to `i64`, and a handle is an `i32`: an `own` or a
  `borrow` of a resource, a `stream` or a `future`.
- The error is at the type that differs, and says what the WIT has there
  and which type within it isn't matched. A pointer, a function pointer, an
  `int` and a `uint` are types of no WIT.
- An interface that isn't there to import is an error at the block that
  names it, as is a function that its interface doesn't have. A library
  imports from any interface of WASI 0.3 or of the WIT in its `wit`
  directory, and the component it is built into has a world that imports
  each of them.
- No function of either block is generic, and no generic function is
  exported.
- The host gives every argument. A default is passed by the Duck call that
  leaves it out, so an `extern` function may have them, an exported one has
  them for Duck callers only, and `start` names a function with no parameters.

### What crosses to the host

A function is declared with what it takes and gives, and the compiler passes
those as the Canonical ABI of the component model has them.

- A value is the wasm values of its scalars, as it is between Duck functions,
  while there are few enough: parameters of up to 16, and a result of one.
  More are passed in memory, laid out as Duck lays them out, by a pointer.
- Nothing is a stack in memory, so what is passed in memory goes through the
  return area: 128 bytes of the component's memory, placed with its literals
  the first time anything needs them. A call of an import stores there the
  parameters that are too many, the host writes its result there, and the
  call reads it into locals as it returns. An exported function stores its
  result there as it returns, which the host reads before it calls anything
  else. So nothing is kept there, and one area serves every call.
- A function that passes more than the area holds is an error where it is
  declared, which says how many bytes it passes. `return` under `[memory]`
  in `Duck.toml` gives the area more. A library is checked with 128.
- The host allocates what it passes that holds a `list` or a `string`: the
  result of an import, the parameters of an export, and those of an export
  that are too many for wasm values. A component whose host does has
  `pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint)
  -> &var u8` in its entry file, or a `pub use` of another file's as that
  name: it is called with `old` and `old_size` as 0, and returns `new_size`
  bytes at a multiple of `align`. Without one the error is where the host
  would first need it.
- What a component passes the host is the component's own to keep or free:
  the host copies a `list` that an export returns and frees nothing.
- An integer of 32 bits or fewer, a `bool`, an enum of either and a handle
  are each a wasm `i32`, as are an `int`, a `uint`, a pointer and a function
  pointer, which no WIT has. The host may give any `i32` for a narrow one,
  which is brought into its range.
- `externref` is an opaque reference of the host of a wasm module, which no
  world has: a component neither takes nor gives one.

## WASI

`duck run` compiles the component of the nearest `Duck.toml` and runs its
`start` function in Wasmtime, which gives it WASI 0.3: the interfaces of
`wasi:cli/imports@0.3.0`. It writes no file.

```duck
extern "$root":                          # built-ins of the component model
	fn set_new() -> i32 = "[waitable-set-new]"
	fn join(waitable: i32, set: i32) = "[waitable-join]"
	fn wait(set: i32, event: &var tuple(i32, i32)) -> i32 = "[waitable-set-wait]"
	fn set_drop(set: i32) = "[waitable-set-drop]"

extern "wasi:cli/stdout@0.3.0":          # an interface, with its version
	fn write_via_stream(data: i32) -> i32          # `write-via-stream`
	fn stream_new() -> i64 = "[stream-new-0]write-via-stream"
	fn stream_write(
		stream: i32,
		bytes: array(u8),                # a `list<u8>`
	) -> i32 = "[async-lower][stream-write-0]write-via-stream"
	fn stream_drop(stream: i32) = "[stream-drop-writable-0]write-via-stream"
	fn future_read(
		future: i32,
		ret: &var result(tuple(), u8),   # its `result<_, error-code>`
	) -> i32 = "[async-lower][future-read-1]write-via-stream"
	fn future_drop(future: i32) = "[future-drop-readable-1]write-via-stream"

extern "wasi:cli/environment@0.3.0":
	fn get_arguments() -> array(string)            # a `list<string>`

extern "wasi:cli/exit@0.3.0":
	fn exit_with_code(status: u8) -> never

let greeting = "Hello,"
let newline = "\n"
let event = &var (0, 0)                  # the waitable, and the code it ends with
let written = &var result(tuple(), u8).ok(())
var heap: uint = 0
var end: uint = 0

pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
	var at = (heap + align - 1) / align * align
	if at + new_size > end:
		let pages = (new_size + module.page_size - 1) / module.page_size
		let first = module.grow(pages)   # only the pages it gives are free
		if first < 0:
			module.unreachable()
		at = first as uint * module.page_size
		end = at + pages * module.page_size
	heap = at + new_size
	module.copy(at as! &var u8, old, old_size)
	return at as! &var u8

fn settle(waitable: i32, code: i32) -> i32:  # the code an operation ends with
	if code != -1:                       # -1: it is not done yet
		return code
	let set = set_new()
	join(waitable, set)
	let _ = wait(set, event)             # blocks until it is
	join(waitable, 0)                    # leaves the set, which is then dropped
	set_drop(set)
	return event.*.1

fn send(stream: i32, bytes: array(u8)):
	var rest = bytes
	while rest.len > 0:
		let code = settle(stream, stream_write(stream, rest))
		let count = (code as u32 >> 4) as uint  # how many bytes were taken
		rest = array(u8)(ptr: (rest.ptr as uint + count) as! &u8, len: rest.len - count)
		if code & 15 != 0:               # the host dropped its end
			return

fn main():                               # `start = "main"` in Duck.toml
	let ends = stream_new()              # a `stream<u8>`: both of its ends
	let stream = (ends >> 32) as i32     # the end that writes
	let future = write_via_stream(ends as i32)  # the host takes the one that reads
	send(stream, greeting)
	for argument in get_arguments():     # allocated with `cabi_realloc`
		send(stream, argument)
	send(stream, newline)
	stream_drop(stream)                  # only then is the future resolved
	let _ = settle(future, future_read(future, written))
	future_drop(future)
	match written.*:
		.ok(_):
			pass
		.err(_):
			exit_with_code(1)
```

- `duck run a -b` gives the program the arguments `a` and `-b`, after its own
  name. It reaches all that `duck` does: its standard streams, its
  environment variables, the network, and every file.
- `wasi:filesystem/preopens` gives two directories to open paths in, each to
  read and write: `.`, the directory `duck run` is in, and then `/`.
- The `start` function is the program. It is called by the `run` of
  `wasi:cli/run`, once the module is instantiated, so that it may call every
  import, and `duck run` exits with 0 when it returns, or with the status it
  gives `wasi:cli/exit`. A program that defines `run` itself, in a
  `pub "wasi:cli/run@0.3.0":` block, names no `start`, and exits with 1 when
  its `run` returns `.err(())`. A trap is an error that names the functions that
  were running. A component of a world that doesn't export `wasi:cli/run`
  doesn't run, nor does one that imports what WASI 0.3 doesn't have: `duck
  build` builds it, for a host that does.
- An `extern` block names an interface that the world imports, with its
  version: for a program, one of `wasi:cli`, `wasi:clocks`,
  `wasi:filesystem`, `wasi:random` or `wasi:sockets` at `0.3.0`. Nothing else
  is there to import. The built-ins that no interface has are of `"$root"`.
- A function has the name its WIT does, which `get_arguments` has without
  being given it. A resource's method is given its own, as in
  `= "[method]descriptor.open-at"`, one that needs no handle is
  `[static]tcp-socket.create`, and `[resource-drop]descriptor` drops a
  handle, which takes it.
- It is declared as the WIT declares it, with the types that those of the
  WIT are: `get_arguments` gives an `array(string)`, which the host has
  `cabi_realloc` allocate.
- An `async func` of the WIT is declared and called as any other is, and
  returns when it is done: `[method]descriptor.open-at` blocks until the file
  is open.
- `duck build` writes the component, with these imports for its host to give
  it.

### Streams and futures

A `stream<T>` and a `future<T>` of the WIT are handles, each an `i32`. No
interface has their functions: they are built-ins, imported from the interface
of a function that has the stream or future in its type, and named for it.

- The name ends with that function's, after the built-in and a number:
  `[stream-new-0]write-via-stream`. The number counts the streams and futures
  of the function's type, its parameters before its result, so the
  `stream<u8>` that `write-via-stream` takes is 0 and the `future` it returns
  is 1.
- `[stream-new-N]` gives both ends of a new stream as an `i64`: the end that
  reads is its low half, and the end that writes its high half. A function
  that takes a stream takes the end that reads, which is then the host's.
- `[async-lower][stream-write-N]` takes the end that writes and an `array(T)`,
  and `[async-lower][stream-read-N]` the end that reads and a `varray(T)` to
  fill. Each gives a code: the count of elements it took or gave, shifted
  left by 4, and in the low 4 bits 0, or 1 once the other end is dropped.
- `[async-lower][future-read-N]` takes a future and a `&var T` to write its
  value to, and gives a code that is 0 once it has.
- A code of -1 says that it isn't done. Its handle is then joined to a set of
  `$root`, with `[waitable-join]`, and `[waitable-set-wait]` blocks until one
  of the set is done, writing that handle and its code to a
  `&var tuple(i32, i32)`. A handle leaves its set by joining the set 0, as it
  must before the set is dropped.
- A future that says how a stream ended is resolved only once the end that
  writes is dropped, with `[stream-drop-writable-N]`: reading it before
  blocks for ever.
- `[stream-drop-readable-N]`, `[future-drop-readable-N]` and the others drop
  a handle, which takes it.

## Duck.toml

`duck new <dir>` creates a component package, and `duck new --lib <dir>` a
library.

```toml
[component]              # the wasm component this package builds
entry = "src/main.duck"  # relative to Duck.toml
output = "build/out.wasm"
start = "main"           # optional: the program, which `duck run` runs
world = "wasi:cli/command@0.3.0"  # optional: what it imports and exports

[memory]                 # optional, as is each key; needs [component]
max = "16MiB"            # sizes: B, KiB, MiB, GiB, TiB, pgs (64 KiB)
static = { start = "1KiB" }  # where literals go from, which is 0 without it
return = "256B"          # the return area, which is 128 bytes without it

[const]                  # optional
fuel = 10000000000       # wasm instructions the constants of one item may run

[library]                # what other packages `use` by name
entry = "src/lib.duck"

[dependencies]           # each must have a [library]
json = { path = "../json" }
xml = { git = "https://example.com/xml.git", tag = "v1.0" }  # or rev; no branches
```

- A component is one of a world, which says what it imports and exports.
  Without a `world` it is a program, of `wasi:cli/command@0.3.0`: it imports
  WASI 0.3 and exports the `run` of `wasi:cli/run`, which calls `start`. A
  `start` is only for a world that exports that `run`.
- A world of the package's own is written in WIT, in the `.wit` files of the
  `wit` directory beside `Duck.toml`, and is named as it is there: `app`, or
  `my:pkg/app@0.1.0` in full. The packages that WIT uses are each a file or a
  directory of `wit/deps`. WASI 0.3 is always there to use and is never
  among them.
- A library has no world: it is built into the components that use it.
- Memory has no `min`: it starts with the pages below `static.start`, those
  its literals take and those its constants grow it by. For one that starts
  larger, have a constant take the pages with `module.grow`.
- A library keeps addresses and lengths in `uint`, never `u32`: they are
  types of their own, whatever is as wide.
