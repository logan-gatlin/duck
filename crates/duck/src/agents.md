# Duck

Indentation-blocked, statically typed, compiled to one WebAssembly module.
Values live in wasm locals and globals, memory is raw pointers into linear
memory, and the host supplies all I/O through `extern`. `duck build` compiles
the package of the nearest `Duck.toml`.

Absent: allocator, GC, standard library, closures, anonymous functions,
methods, traits, overloading, default arguments, varargs, `match`, ternary,
ranges, exceptions, char type, string operations.

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

fn area(w: f64, h: f64) -> f64:
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
- Keywords: `pub fn let var return if else while for in break continue pass
  struct enum extern import module and or not true false as`. No item is
  named `array`, `varray`, `tuple` or `type`.

## Types

- `i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 bool`. Integer arithmetic wraps.
  Numeric types never mix (`u8 + i32` is an error): convert with `as`.
- `tuple(A, B)`: built `(a, b)`, read `t.0`. Unit is `tuple()`, written `()`.
- `&T` reads its pointee and `&var T` also writes it. Both are unchecked
  `u32` addresses, and `0` is null.
- `array(T)`: a view of `len: u32` and `ptr: &T` that owns nothing.
  `varray(T)` has a `ptr: &var T`, so its elements are assignable. Strings
  are `array(u8)` of UTF-8.
- `fn(A, B) -> R`: a function pointer. `fn(A)` returns nothing.
- `type`: a type as a value, with `size: u32` and `align: u32`, as in
  `Point.size`, `(&Point).size` and `i64.align`.
- `externref`: an opaque host reference. It is never stored in memory or
  compared.
- `Name`, `Name(T)`, `mod.Name`: structs and enums, passed by value like
  tuples and arrays.
- `enum(T) Name:` makes each member a constant of any type `T`. Integer
  members count up from the one before, and other types need every value.
  Enums support `Name.member`, `==`, `!=`, `e as T` and `for m in Name`.
  Nothing converts a `T` to the enum.

A `&var T` is accepted as a `&T`, and a `varray(T)` as an `array(T)`, for the
type as a whole only: a `tuple(&var T, i32)` is not a `tuple(&T, i32)`, and a
`fn(&T)` is not a `fn(&var T)`.

## Literals and globals

**String and array literals belong in global initializers and field defaults
only.** In a function, name a global.

```duck
let greeting = "hello"             # array(u8)
let primes: array(u16) = [2, 3, 5]
let empty: array(i32) = []         # [] needs an annotation
let SIZE: u32 = 1024
let buf: varray(u8) = [0; SIZE]    # writable; zeros add nothing to the wasm

fn f(i: u32) -> u8:
	buf[i] = greeting[i]           # a u32 index, bounds checked
	return buf[0]
```

- A literal is a read-only `array` unless its global is annotated `varray`.
- An integer literal takes the type expected of it, which may be a float or a
  pointer (`let p: &u8 = 16`), and is otherwise `i32`. A float literal is
  `f64` by default and has a digit on each side of the `.`.
- A global initializer is constant: literals, operators, casts, constructors,
  function names and earlier `let` globals. Calls and `var` globals are out.
- A field default is constant too. It and other initializers use only the
  defaults of structs declared earlier. A `varray` literal in one is empty,
  as every value would share its elements.
- Only a constructor applies defaults. Memory that is cast to a struct holds
  whatever was there.

## Operators

Loosest to tightest, the binary ones left associative: `|>`, `or`, `and`,
`not`, `== != < <= > >=`, `|`, `^`, `&`, `<< >>`, `+ -`, `* / %`, `as`,
prefix `- ~ & &var`, postfix `f(x) a[i] x.f t.0 p.*`.

- `%` and `~` take integers, and unary `-` takes signed integers and floats.
  Integer division by zero traps.
- `==` and `!=` compare any one type structurally, arrays by length and
  elements. `< <= > >=` compare numbers and pointers.
- `as` converts number to number (float to integer saturates, NaN gives 0),
  `bool` to integer, pointer to pointer (how a `&T` becomes a `&var T`),
  `array(T)` to `varray(T)` and back, `i32` or `u32` to and from pointers and
  function pointers, function pointer to function pointer, and an enum to its
  value type. Nothing converts to `bool`: write `x != 0`.

## Pointers and memory

```duck
struct Node:
	val: i32
	next: &Node

var heap: u32 = 65536

fn alloc(t: type) -> &var u8:          # bump from an address you pick
	heap = (heap + t.align - 1) / t.align * t.align
	heap += t.size
	return (heap - t.size) as &var u8

fn push(head: &Node, v: i32) -> &Node:
	let n = alloc(Node) as &var Node
	n.* = Node(val: v, next: head)     # `p.*` is the whole pointee
	n.val += 1                         # fields auto-dereference
	let r: &var i32 = &var n.val       # `&place` gives a `&T`
	r.* = 0
	if head != 0:
		return head
	return n

fn view(p: &i32, len: u32) -> array(i32):
	return array(i32)(len: len, ptr: p) # slice by building a new view
```

- `&` and `&var` take the address of `p.field`, `p.*` and `a[i]` only. Locals,
  parameters and globals have no address.
- A write needs a `var` local, a `&var` or a `varray`, and only the last
  pointer or array on the way to the place decides: with `next: &var Node`,
  `p.next.val = 1` works through a `p: &Node`. `let` and `var` govern the
  binding, not the pointee.
- Pointer arithmetic is `((p as u32) + 4) as &T`.
- Layout follows C, and `bool` is 1 byte.
- The only runtime checks are array bounds and division by zero, which trap.
- Literals fill the static section from address 0. Memory starts as the
  fewest pages that hold it, which is none without literals, so call
  `module.grow` before using addresses past it. `[memory]` in `Duck.toml`
  overrides both.

`module` is built in. Its functions are single wasm instructions and have no
pointers.

- `module.page_size`, `module.min`, `module.max`: `u32` constants for the
  bytes in a page and the pages memory starts with and may grow to.
- `module.size() -> u32` and `module.grow(pages: u32) -> i32` count pages.
  `grow` gives the old size, or -1.
- `module.memory() -> varray(u8)` is all of memory from address 0, and
  `module.static` is an `array(u8)` of the static section.
- `module.fill(dst: &var u8, value: u8, len: u32)` and
  `module.copy(dst: &var u8, src: &u8, len: u32)`. `copy` handles overlap.
- `module.unreachable()` traps, and ends a function as `return` does.
- `module.count_leading_zeros(x)` and `module.count_trailing_zeros(x)` take
  any integer type and give that type.

## Generics

```duck
struct(T) Box:
	value: T

fn(T) larger(a: T, b: T) -> T:     # no bounds: each call's types must suit the body
	if a > b:
		return a
	return b

fn(T) zero() -> T:
	return 0 as T

fn demo() -> u8:
	let b = Box(u8)(value: 1)      # generic structs always take type arguments
	let z = zero(u8)()             # f(Types)(args) when arguments can't infer them
	return larger(z, b.value)
```

- A generic body is checked as declared, where `T` is only itself. What no
  type could make right is an error there, like a `T` returned as a `Box(T)`.
  What some types make right, like `a > b`, is checked for each call's type
  arguments, and an error is reported at the call.
- In a generic body `T` is also a value (`T.size`), a constructor (`T(x: 1)`)
  and an enum (`T.ok`). `T.size` and `T.align` are always those of the type.
- A field default never names `T`, and a field holding a `T` by value has
  none. `head: &var T = 0` and `items: varray(T) = []` are fine.
- `p: &T` takes a `&var i32` with `T` as `i32`, and `array(T)` a `varray(i32)`.
  Nothing is generic over writability: write both, or cast.

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

- A call through a pointer takes positional arguments only.
- `extern` functions have pointers too. Calling a zeroed pointer traps.
- With a generic `f`, `f(x)(y)` reads `x` as type arguments, so bind `f(x)`
  to a name before calling what it returns.

## Pipes

```duck
fn add(a: i32, b: i32) -> i32:
	return a + b

fn demo(n: i32) -> i32:
	return n * 2
		|> add(_, _) - 1           # `_` is the piped value, evaluated once
		|> _ / 2                   # a deeper line starting with `|>` continues
```

- The body uses `_` at least once: `x |> f(_)`, never `x |> f`.
- A `_` belongs to the nearest pipe: in `x |> f(_, y |> g(_))` the second is
  `y`.
- A piped literal is typed before the body is read: `1 as u8 |> byte(_)`.

## Modules

- `import "dir/file.duck"` resolves from the importing file and binds `file`.
  `as name` renames it, and is required when the stem isn't an identifier.
- `import json` binds the library of the `Duck.toml` dependency `json`. Files
  of one package import each other by path only.
- `pub` items are reached as `mod.item`: `geo.Point(x: 1, y: 2)`,
  `geo.Color.red`. A `pub` item's signature uses only `pub` types.
- Another file constructs a struct only if every private field has a default,
  and never gives a private field a value.
- `pub import "x.duck"` exposes `x` to importers, as `this.x.item`.
- Imports form no cycles.

## Host

```duck
extern "js":                               # wasm import module
	fn print(s: array(u8)) = "print_bytes" # the host's name for it
	pub fn get() -> externref              # callable from other files

pub fn tick(dt: f64) -> f64:               # exported as "tick"
	return dt
```

- The entry file's `pub` functions and globals are the exports, generic
  functions excepted. Also exported are `memory` and, once any function
  pointer is taken, `table`: the host calls pointer `i` as
  `table.get(i)(...)`. No `pub` item is named either.
- Integers of 32 bits or fewer, `bool`, pointers and function pointers are
  wasm `i32`. `i64`, `f32`, `f64` and `externref` are themselves, and an enum
  is its value type. Structs, tuples, arrays and `type` are one wasm value
  per scalar, in field order: `fn f(s: array(u8)) -> Point` is
  `(i32 len, i32 ptr) -> (f32, f32)`.
- An exported aggregate global is one wasm global per scalar, named with
  dots: `origin.x`, `name.len`, `name.ptr`.

## Duck.toml

`duck new <dir>` creates a module package, and `duck new --lib <dir>` a
library.

```toml
[module]                 # the wasm module this package builds
entry = "src/main.duck"  # relative to Duck.toml
output = "build/out.wasm"
start = "main"           # optional: run on instantiation

[memory]                 # optional, as is each key; needs [module]
min = "1pgs"             # sizes: B, KiB, MiB, GiB, pgs (64 KiB)
max = "16MiB"
static = { start = "0B", end = "64KiB" }  # where literals go

[library]                # what other packages `import` by name
entry = "src/lib.duck"

[dependencies]           # each must have a [library]
json = { path = "../json" }
xml = { git = "https://example.com/xml.git", tag = "v1.0" }  # or rev; no branches
```
