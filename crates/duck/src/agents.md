# Duck

Indentation-blocked, statically typed, compiled to one WebAssembly module.
Values live in wasm locals and globals, memory is raw pointers into linear
memory, and the host supplies all I/O through `extern`. `duck build` compiles
the package of the nearest `Duck.toml`, and `duck run` runs it with WASI.
`duck format` lays its files out as the examples here are.

Absent: allocator, GC, standard library, closures, anonymous functions,
methods, traits, overloading, varargs, ternary, ranges, exceptions, char type,
string operations.

## Syntax

```duck
extern:                          # host functions, from wasm module "env"
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
- `int` and `uint`: integers as wide as an address, which is 32 bits, or 64
  with `memory64` in `Duck.toml`. They count bytes and elements, and are
  types of their own: `uint + u32` is an error too.
- `tuple(A, B)`: built `(a, b)`, read `t.0`. Unit is `tuple()`, written `()`.
- `&T` reads its pointee and `&var T` also writes it. Both are unchecked
  addresses, which `as!` makes of any address. There is no null: `0` is an
  address like any other.
- `option(T)`: the union of `none` and `some: T`. `result(T, E)`: the union
  of `ok: T` and `err: E`. Both are built in, and are unions in every way.
- `array(T)`: a view of `ptr: &T` and `len: uint` that owns nothing.
  `varray(T)` has a `ptr: &var T`, so its elements are assignable.
- `string`: an alias of `array(u8)`, which holds UTF-8.
- `fn(A, B) -> R`: a function pointer. `fn(A)` returns nothing.
- A type has a `size: uint` and an `align: uint`, as in `Point.size`,
  `(&Point).size` and `i64.align`. It is no value: `type` is only the type of
  a function's parameter, which makes it a type parameter.
- `externref`: an opaque host reference. It is never stored in memory or
  compared.
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
  `f(return 1)` and `let x = return 1` are accepted, and return 1. `never`
  is no type to write.
- A `break` and a `continue` are expressions as a `return` is, with no value
  to take, and each is a `never`. One in the condition of a `while` is of
  that loop: `while more() or break:`.
- A function with a result ends by a `return` wherever it ends. The right
  side of `and` and `or` may not be evaluated, so a `return` there ends
  nothing: `half` needs its last line.

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
  `int` and a `uint` are each 4 bytes, or 8 with `memory64`.
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

```duck
extern "js":                               # wasm import module
	fn print(s: array(u8)) = "print_bytes" # the host's name for it
	pub fn get() -> externref              # callable from other files

pub fn tick(dt: f64) -> f64:               # exported as "tick"
	return dt
```

- The `pub` functions and globals the entry file defines are the exports,
  generic functions excepted. Also exported are `memory` and, once any function
  pointer is taken, `table`: the host calls pointer `i` as
  `table.get(i)(...)`. No `pub` item is named either.
- A `pub use` in the entry file exports the function or global it names, from
  whichever file, as the name it binds: `pub use alloc.realloc as cabi_realloc`
  exports `cabi_realloc`. One named twice is exported as both. A generic or
  `extern` function isn't exported, as a `pub` one of the entry file isn't.
- The host gives every argument. A default is passed by the Duck call that
  leaves it out, so an `extern` function may have them, an exported one has
  them for Duck callers only, and `start` names a function with no parameters.
- Integers of 32 bits or fewer and `bool` are wasm `i32`. So are `int`,
  `uint`, pointers and function pointers, which are `i64` with `memory64`: a
  JS host then passes each as a `BigInt`, as in `table.get(1n)`. `i64`,
  `f32`, `f64` and `externref` are themselves, and an enum is its value type.
  Structs, tuples and arrays are one wasm value per scalar, in field
  order: `fn f(s: array(u8)) -> Point` is `(i32 ptr, i32 len) -> (f32, f32)`.
- An exported aggregate global is one wasm global per scalar, named with
  dots: `origin.x`, `name.ptr`, `name.len`.
- A union is an `i32` that counts its variants from 0, then the values its
  variants share, as the Canonical ABI of the component model flattens a
  variant. Each variant's scalars are held in order from the first, and each
  shared value is as wide as what any variant has there: an `i32` and an
  `f32` share an `i32`, and any others that differ an `i64`. `union Shape`
  with `circle: f32` and `rect: tuple(f32, i64)` is `(i32, f32, i64)`, and
  `result(i32, f32)` is `(i32, i32)`. `option(f32)` is `(i32, f32)` with 0
  for `none`, its first variant, so that zeroed memory holds it, and
  `result(T, E)` has 0 for `ok`.
- A float held in an integer is its bits, and what is narrower than the
  `i64` that holds it has zeroes above it, which are ignored when it's read.
  The values the held variant doesn't use are zero in every value Duck
  builds and are never read: the host may pass anything in them.
  `externref`s share only values of their own, which come after the rest and
  are null where unused. A count that no variant has matches no arm, and
  memory keeps only its low byte.
- A union is returned as these values, not through a pointer as the
  Canonical ABI returns one.
- An exported `shape` is the globals `shape`, `shape.0` and `shape.1`.

## WASI

`duck run` compiles the module of the nearest `Duck.toml` and runs its `start`
function in Wasmtime, which gives it WASI 0.2: the interfaces of
`wasi:cli/imports@0.2.12`. It writes no file.

```duck
union StreamError:                       # `variant stream-error`
	last_operation_failed: i32           # holds an `own<error>`, a handle
	closed

extern "wasi:cli/stdout@0.2.12":         # an interface, with its version
	fn get_stdout() -> i32 = "get-stdout"  # an `own<output-stream>`

extern "wasi:io/streams@0.2.12":
	fn write(
		stream: i32,                     # the `borrow<output-stream>` of a method
		contents: array(u8),             # a `list<u8>`
		ret: &var result(tuple(), StreamError),  # its `result<_, stream-error>`
	) = "[method]output-stream.blocking-write-and-flush"

extern "wasi:cli/environment@0.2.12":
	fn get_arguments(ret: &var array(array(u8))) = "get-arguments"  # `list<string>`

extern "wasi:cli/exit@0.2.12":
	fn exit(status: u8) = "exit-with-code"

let greeting = "Hello,"
let newline = "\n"
let written = &var result(tuple(), StreamError).ok(())
let arguments: &var array(array(u8)) = &var []
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

fn main():                               # `start = "main"` in Duck.toml
	let out = get_stdout()
	write(out, greeting, written)
	get_arguments(arguments)             # allocates with `cabi_realloc`
	for argument in arguments.*:
		write(out, argument, written)
	write(out, newline, written)
	match written.*:
		.ok(_):
			pass
		.err(_):
			exit(1)
```

- `duck run a -b` gives the program the arguments `a` and `-b`, after its own
  name. It reaches all that `duck` does: its standard streams, its
  environment variables, the network, and every file.
- `wasi:filesystem/preopens` gives two directories to open paths in, each to
  read and write: `.`, the directory `duck run` is in, and then `/`.
- The `start` function is the program. It runs once the module is
  instantiated, so that it may call every import, and `duck run` exits with 0
  when it returns, or with the status it gives `wasi:cli/exit`. A trap is an
  error that names the functions that were running. A module without a
  `start` doesn't run, nor does one with `memory64`.
- An `extern` block names an interface of `wasi:cli`, `wasi:io`,
  `wasi:clocks`, `wasi:filesystem`, `wasi:random` or `wasi:sockets` with the
  version `0.2.12`, or an earlier `0.2` one that it stands for. Nothing else
  is there to import: an `extern` function of `env` is an error.
- A function has the name its WIT does: `get-stdout`, a resource's method as
  `[method]output-stream.write`, and `[resource-drop]output-stream` to drop a
  handle, which takes it.
- It is declared as the Canonical ABI lowers it, which is how Duck passes
  values. A handle, `own` or `borrow`, is an `i32`, and a `char` a `u32`. A
  `list<T>` is an `array(T)` and a `string` an `array(u8)`. A `record` is a
  struct, a `variant` a union, an `enum` an `enum(u8)`, and `tuple`, `option`
  and `result` are Duck's own, each with its fields, variants or members in
  order. `flags` are the narrowest of `u8`, `u16` and `u32` with a bit for
  each, from the lowest. A `_` is `tuple()`.
- A function that returns more than one wasm value takes a `&var` to its
  result as a last parameter instead, and returns nothing: Duck lays a type
  out in memory as the Canonical ABI does. `-> i32` stays for a handle, and
  `ret: &var array(u8)` is for a `string`. Parameters that come to more than
  16 wasm values are one pointer to a tuple of them.
- The host returns a `list` or a `string` in memory that it has the module
  allocate. A module that imports such a function has `pub fn cabi_realloc` in
  its entry file, as above, or a `pub use` of another file's as that name: it
  is called with `old` and `old_size` as 0, and returns `new_size` bytes at a
  multiple of `align`.
- `duck build` writes the module as it does any other, with these imports
  for its host to give it.

## Duck.toml

`duck new <dir>` creates a module package, and `duck new --lib <dir>` a
library.

```toml
[module]                 # the wasm module this package builds
entry = "src/main.duck"  # relative to Duck.toml
output = "build/out.wasm"
start = "main"           # optional: run on instantiation, and by `duck run`

[memory]                 # optional, as is each key; needs [module]
memory64 = true          # 64-bit addresses, which are 32-bit without it
max = "16MiB"            # sizes: B, KiB, MiB, GiB, TiB, pgs (64 KiB)
static = { start = "1KiB" }  # where literals go from, which is 0 without it

[const]                  # optional
fuel = 10000000000       # wasm instructions the constants of one item may run

[library]                # what other packages `use` by name
entry = "src/lib.duck"

[dependencies]           # each must have a [library]
json = { path = "../json" }
xml = { git = "https://example.com/xml.git", tag = "v1.0" }  # or rev; no branches
```

- Memory has no `min`: it starts with the pages below `static.start`, those
  its literals take and those its constants grow it by. For one that starts
  larger, have a constant take the pages with `module.grow`.
- `memory64` builds a wasm memory64 module, whose memory and table are
  addressed with 64 bits: sizes may pass 4GiB, and `int`, `uint`, pointers
  and function pointers are 64 bits wide. A `uint` past 4294967295 is an
  error without it.
- A library builds as the module that uses it does, so it keeps addresses and
  lengths in `uint`, never `u32` or `u64`. On its own it is checked with
  32-bit addresses.
