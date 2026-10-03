# Duck: an overview for agents

Duck is a small, statically typed language with Python-like indentation that
compiles to a WebAssembly module. It has no runtime, no garbage collector and
no standard library. Values live in wasm locals and globals. Memory is only
reached through raw pointers into linear memory, and the host supplies all I/O
through `extern` imports.

Every ```duck block below compiles as a file of its own.

## CLI

- `duck new <dir>` creates a module: `Duck.toml`, `src/main.duck` and a
  `.gitignore`. `duck new --lib <dir>` creates a library instead:
  `Duck.toml`, `src/lib.duck` and a `.gitignore`.
- `duck build` compiles the package of the nearest `Duck.toml` in this
  directory or a parent. It writes the module's wasm to `output`. A package
  with only a `[library]` is type checked, and nothing is written.
- `duck agents` prints this overview.

Errors look like `src/main.duck:3:5: error: expected `i32`, found `bool``.
An error inside a generic function is followed by one
`note: in `name(T)`, called here` line per instance it is in. All errors of
a stage are reported at once. The stages are lexing and parsing every file,
then type checking.

## Duck.toml

```toml
[module]                 # the wasm module this package builds
entry = "src/main.duck"  # relative to Duck.toml
output = "build/out.wasm"
start = "main"           # optional: run on instantiation; takes and returns nothing

[memory]                 # required with [module], forbidden without it
min = "1pgs"             # sizes: B, KiB, MiB, GiB, or pgs (64 KiB pages)
max = "16MiB"            # optional; omit to grow without limit
static = { start = "0B", end = "64KiB" }  # where literals go; must end within `min`

[library]                # optional: what other packages `import` by name
entry = "src/lib.duck"

[dependencies]           # each must have a [library]
json = { path = "../json" }
xml = { git = "https://example.com/xml.git", tag = "v1.0" }  # or rev = "<hash>"; no branches
```

A package needs a `[module]`, a `[library]`, or both. Git dependencies are
cached under `$XDG_CACHE_HOME/duck/git`, or `~/.cache/duck/git`.

## Lexical structure

- Blocks start with `:` at the end of a line and are indented under it, as in
  Python. Use tabs or spaces, but each line's indentation must extend or match
  an enclosing block's. Line breaks and indentation mean nothing inside
  `()` and `[]`. There are no semicolons.
- An empty block is written `pass`.
- Comments run from `#` to the end of the line.
- Integers: `42`, `1_000`, `0xff`, `0o17`, `0b1010`. Floats: `1.5`, `2e3`,
  `1.5e-2`. A float needs digits on both sides of the `.`.
- Strings: `"..."` with the escapes `\n \r \t \0 \\ \" \'` and `\u{1F986}`.
  They are UTF-8 bytes. There is no char type.
- Lists of arguments, parameters, fields and elements allow a trailing comma.
- Keywords: `pub fn let var return if else while for in break continue pass
  struct enum extern import module and or not true false as`.

## Items

A file holds these items, in any order:

```duck
extern:                            # host functions, from wasm module "env"
	fn log(n: i32)

pub let LIMIT = 100                # immutable global
var count: i32 = 0                 # mutable global

pub struct Point:
	pub x: f32
	pub y: f32

enum(u8) Color:
	red
	green

pub fn main():
	count += 1
	log(count)
```

- `import` is also an item; see "Modules and packages".
- Items are private to their file unless marked `pub`. Struct fields are
  private unless marked `pub`.
- Every `pub` function and global of the entry file is exported from the wasm
  module. The memory is exported as `memory`, so no `pub` item may be named
  that. Generic functions are never exported.
- Items may be used before they are declared, except that a global's
  initializer can only read earlier globals.

## Types

| Type | Notes |
| --- | --- |
| `i8 i16 i32 i64 u8 u16 u32 u64` | Integers. Arithmetic wraps at the type's width. |
| `f32 f64` | IEEE floats. |
| `bool` | `true`, `false`. |
| `tuple()` | Unit: the return type of functions without one. Its value is `()`. There is no `unit` or `void`. |
| `tuple(A, B, ...)` | Two or more elements. Built with `(a, b)`, read with `t.0`. Structural. |
| `&T` | A pointer: a `u32` address into linear memory. Nothing checks it. |
| `array(T)` | A slice that owns nothing: the fields `len: u32` then `ptr: &T`. |
| `type` | A type used as a value: the fields `size: u32` and `align: u32`. |
| `externref` | An opaque host reference. It can never be stored in memory. |
| `Name`, `Name(T, ...)` | Structs and enums, plain or generic. |
| `mod.Name` | A type from an imported module. |

There are no implicit conversions. Integers of different widths or
signedness don't mix, so `a + b` with `a: u8` and `b: i32` is an error. Convert
with `as`.

## Literals and inference

- An integer literal takes the type it is expected to have: from an
  annotation, a parameter, or the other operand of a binary operator. With
  nothing to go by it is `i32`. A float literal is `f64` by default.
- An integer literal can stand where a float is expected (`let x: f32 = 1`) or
  where a pointer is expected (`let p: &u8 = 16`).
- Out-of-range literals are errors: `let b: u8 = 256`.
- **String and array literals are only allowed in global initializers.** They
  are placed in the static data section, and the global holds the resulting
  `array`. To use one in a function, bind it to a global first.

```duck
let greeting = "hello"                    # array(u8)
let primes: array(u16) = [2, 3, 5, 7]
let names = ["ann", "bob"]                # array(array(u8))
let empty: array(i32) = []                # [] needs a type annotation

fn first_prime() -> u16:
	return primes[0]
```

## Expressions and operators

These are listed from loosest to tightest binding. Binary operators are left
associative.

| Precedence | Operators |
| --- | --- |
| 1 | `or` (short-circuits, `bool` only) |
| 2 | `and` (short-circuits, `bool` only) |
| 3 | `not` (prefix) |
| 4 | `== != < <= > >=` |
| 5 | `\|` |
| 6 | `^` |
| 7 | `&` |
| 8 | `<< >>` |
| 9 | `+ -` |
| 10 | `* / %` |
| 11 | `x as T` |
| 12 | prefix `-`, `~`, `&` |
| 13 | postfix: call `f(x)`, index `a[i]`, field `x.f`, `t.0`, deref `p.*` |

Some consequences of this table:

- `not a == b` is `not (a == b)`.
- `a + b as i64` is `a + (b as i64)`.
- `-x as u8` is `(-x) as u8`.
- `a & mask == 0` is `(a & mask) == 0`. Unlike C, bitwise operators bind
  tighter than comparisons.

Rules for each operator:

- `+ - * /` work on numbers. `%` only works on integers. Integer division
  truncates, and dividing by zero traps. `>>` is arithmetic on signed types and
  logical on unsigned ones. The shift amount wraps at the type's width.
- Unary `-` works on signed integers and floats, but not unsigned integers.
  `~` works on integers.
- `< <= > >=` compare numbers, and pointers as unsigned addresses.
- `==` and `!=` compare values of any one type: structs and tuples field by
  field, arrays by length and elements, enums by bits, and types by size and
  alignment. Anything that holds an `externref` can't be compared.
- `as` converts between any two numeric types. Float to integer saturates,
  and NaN becomes 0. `bool` converts to integers. `i32` and `u32` convert to
  and from pointers. Any pointer converts to any other pointer, and any enum to
  its value type. Every type converts to itself. Nothing converts to `bool` or
  to an enum, so write `x != 0` instead.
- There is no ternary or conditional expression. `if` is a statement.

## Statements

```duck
extern:
	fn log(n: i32)

fn demo(n: i32) -> i32:
	let a = n * 2               # immutable binding
	var total = 0               # mutable binding
	let (q, r) = (n / 3, n % 3) # tuple patterns; `_` discards
	total += a + q + r          # also -= *= /= %=  (no |= &= <<= ...)
	if total > 10:
		log(total)
	else if total < 0:
		return 0
	else:
		pass
	var i = 0
	while i < n:
		i += 1
		if i == 5:
			continue
		if i == 8:
			break
	let x = 1
	let x = x + 1               # shadowing is allowed; bindings are block scoped
	return total + x
```

- Conditions must be `bool`.
- `for x in xs:` iterates over an `array(T)`, copying each element into an
  immutable `x`. `for m in SomeEnum:` visits each member in order, and the
  loop is unrolled at compile time. There are no ranges, so count with
  `while`.
- A function with a return type must return on every path. `while true:`
  without a `break` counts as never finishing.
- Parameters are immutable. Copy one into a `var` to change it.
- An expression used as a statement discards its value.

## Functions

```duck
fn area(w: f64, h: f64) -> f64:
	return w * h

fn caller() -> f64:
	let a = area(2.0, 3.0)
	let b = area(h: 3.0, w: 2.0) # labels may reorder arguments
	return area(2.0, h: a + b)   # positional arguments come before labelled ones
```

- Arguments are evaluated in the order they are written, whatever order the
  labels put them in.
- Functions are not values. There are no closures, methods, overloading,
  default arguments or varargs. Recursion is fine.
- Structs, tuples and arrays are passed and returned by value. The function
  copies them, and each one is split into its scalars at the wasm boundary.

## Structs

```duck
pub struct Vec2:
	pub x: f32
	pub y: f32

fn add(a: Vec2, b: Vec2) -> Vec2:
	return Vec2(x: a.x + b.x, y: a.y + b.y) # every field, by label

fn shift(v: Vec2) -> Vec2:
	var w = v
	w.x += 1.0                               # fields of a `var` are assignable
	return w
```

- Construct a struct with every field labelled. A struct with any private
  field can only be constructed inside its own module.
- A struct may not contain itself by value. Use a pointer, as in
  `next: &Node`.
- A `pub` item's signature or type may only use `pub` types.

## Pointers and memory

Linear memory starts as `min` pages. Literals occupy the static section
(`[memory] static`), which by default is the first 64 KiB, starting at
address 0. **There is no allocator.** Bump-allocate from an address you pick
past the static section, or ask the host for memory.

```duck
struct Node:
	val: i32
	next: &Node

var heap: u32 = 65536 # past the default static section; needs min > 1 page

fn alloc(t: type) -> &u8:
	heap = (heap + t.align - 1) / t.align * t.align
	let p = heap as &u8
	heap += t.size
	return p

fn push(head: &Node, v: i32) -> &Node:
	let n = alloc(Node) as &Node
	n.* = Node(val: v, next: head) # store a whole struct through a pointer
	return n

fn sum(list: &Node) -> i32:
	var total = 0
	var p = list
	while p != 0:                  # 0 is the null address
		total += p.val             # fields auto-dereference through any number of &
		p = p.next
	return total

fn second_field(n: &Node) -> &&Node:
	return &n.next                 # & only takes addresses of memory behind a pointer
```

- `p.*` reads or writes the whole pointee.
- `&place` works on `p.field`, `p.*` and `a[i]`. It does not work on locals,
  parameters or globals, which aren't in memory.
- There is no pointer arithmetic. Write `((p as u32) + 4) as &T`.
- Memory layout follows C: fields in declaration order, each aligned to its
  own alignment, with the struct padded to its largest alignment. `bool` is 1
  byte.
- Nothing checks pointers. The only runtime checks are array bounds and
  division by zero, which trap.

`module` has the memory's constants and functions. The functions compile to
single wasm instructions at each call, not to wasm functions.

```duck
fn reserve(bytes: u32) -> bool:
	let pages = (bytes + module.page_size - 1) / module.page_size
	return module.grow(pages) != -1  # grow gives the old size in pages, or -1

fn clear(buf: array(u8)):
	module.fill(buf.ptr, 0, buf.len)
```

- `module.page_size`, `module.min` and `module.max` are `u32` constants:
  bytes per page, and the pages memory starts with and may grow to. `max` is
  the largest `u32` when Duck.toml sets none.
- `module.memory()` is an `array(u8)` of all current memory, from address 0.
- `module.size() -> u32` is the current size in pages, and
  `module.grow(pages: u32) -> i32` adds pages (`memory.size`, `memory.grow`).
- `module.fill(dst: &u8, value: u8, len: u32)` and
  `module.copy(dst: &u8, src: &u8, len: u32)` are `memory.fill` and
  `memory.copy`. `copy` handles overlap. Out-of-bounds ranges trap.
- `module.unreachable()` traps. As a statement of its own, it ends a function,
  so a function that returns a value needs no `return` after it.

## Arrays and strings

```duck
let text = "duck"

fn count(s: array(u8), c: u8) -> u32:
	var n: u32 = 0
	for b in s:
		if b == c:
			n += 1
	return n

fn view(p: &i32, len: u32) -> array(i32):
	return array(i32)(len: len, ptr: p) # build a view over existing memory

fn demo() -> u32:
	let i: u32 = 2
	let c = text[i]                     # the index must be u32; it is bounds checked
	return count(text, c) + text.len
```

- `a.len` and `a.ptr` are ordinary fields. Slice by building a new
  `array(T)(len:, ptr:)`.
- Strings are `array(u8)` of UTF-8. There are no string operations, so write
  them over bytes.
- `module.static` is an `array(u8)` covering the whole static section.

## Enums

```duck
enum(i8) Code:
	ok           # 0
	warn = 5
	fatal        # 6: integer members count up from the previous one

enum(f32) Scale:
	half = 0.5   # members of non-integer enums all need values
	full = 1.0

fn worst(c: Code) -> bool:
	return c == Code.fatal

fn total() -> i32:
	var sum = 0
	for c in Code:
		sum += c as i8 as i32
	return sum
```

- `enum(T) Name:` gives each member a constant value of type `T`, which may
  be any type, including a struct or tuple. Members must have distinct values.
- Enum values are laid out like `T`. Only `==` and `!=` work on them, and
  `e as T` gets the value. There is no conversion from `T` back to the enum,
  and no `match`.

## Generics

Generics are monomorphized. Each distinct list of type arguments gets its own
copy, and **each copy's body is type checked separately**. There are no trait
bounds: a body is valid for `T` if it type checks with `T` substituted, which
is duck typing.

```duck
struct(T) Box:
	value: T

fn(T) id(x: T) -> T:
	return x

fn(T) larger(a: T, b: T) -> T:
	if a > b:
		return a
	return b

fn(T) zero() -> T:
	return 0 as T

fn demo() -> u8:
	let b = Box(i32)(value: 1)  # generic structs always need type arguments
	let x = id(b)               # type arguments are inferred from the arguments
	let y = larger(3, x.value)
	let z: u8 = zero(u8)()      # or given explicitly: f(Types)(args)
	return z + larger(1, 2 as u8)
```

- Inside a generic function, a type parameter works as a type (`let v: T`),
  as a value (`T.size`), as a constructor (`T(x: 1)`), and to reach enum
  members (`T.ok`).
- A call that gives a type parameter no argument type to infer from must give
  explicit type arguments.
- Recursion must not instantiate ever larger types, as in `f((x, x))`.

## Types as values

A type written where a value belongs has type `type`, with the fields `size`
and `align`. This is how allocators and `sizeof` work:

```duck
struct Point:
	x: f32
	y: f64

fn bytes() -> u32:
	let t: type = Point
	return t.size + (&Point).size + array(u8).size + i64.align
```

## The host: extern and exports

```duck
extern "js":                         # wasm import module; the default is "env"
	fn now() -> f64
	fn print(s: array(u8)) = "print_bytes" # import a host function under another name
	pub fn get() -> externref        # pub lets other files call it

pub fn tick(dt: f64) -> f64:         # exported as "tick"
	return now() + dt
```

How Duck types map to wasm values:

| Duck | wasm |
| --- | --- |
| `i8 i16 i32 u8 u16 u32 bool`, pointers, enums of those | `i32` |
| `i64 u64` | `i64` |
| `f32` | `f32` |
| `f64` | `f64` |
| `externref` | `externref` |
| structs, tuples, `array(T)`, `type` | one wasm value per field, in order |
| `tuple()` | nothing |

So `fn f(s: array(u8)) -> Point` is `(i32 len, i32 ptr) -> (f32, f64)` in
wasm. A host function's narrow results are masked or sign-extended into
range.

Exported globals that are aggregates are split into one global per scalar,
named with dots: `pub let origin = Point(...)` exports `origin.x` and
`origin.y`, and a `pub let` string exports `name.len` and `name.ptr`. A
global's initializer must be a compile-time constant. It may use literals,
operators, casts, struct and tuple constructors, and earlier `let` globals. It
may not use calls or `var` globals.

## Modules and packages

Each file is a module with its own namespace.

- `import "path/to/file.duck"` is resolved relative to the importing file and
  binds the file's stem (`file`). Add `as name` to choose the name, which you
  must do when the stem isn't an identifier.
- `import json` imports the `[library]` of the dependency `json` from
  `Duck.toml`. A package's files may only import each other by path. Files of
  other packages are reached through their library.
- Refer to a module's `pub` items as `mod.item`: `util.add(1, 2)`,
  `geo.Point(x: 1.0, y: 2.0)`, `let c: geo.Color = geo.Color.red`.
- `pub import "x.duck"` lets importers of this module reach `x` through it,
  as `this.x.item`.
- Imports may not form a cycle. An imported module's globals are initialized
  before those of the module that imports it.

## Not in the language

There are no heap allocators, garbage collection, closures, first-class
functions, methods, traits or interfaces, operator overloading, `match`,
exceptions or panics, null safety, ranges, a char type, string operations, a
standard library, or compile-time `const` beyond globals. Don't write any of
them. Build what you need from structs, pointers, `while` and host functions.

## Common mistakes

- Writing a string or `[...]` literal inside a function. Bind it to a global.
- Mixing integer types without `as`: `let i: u32 = ...; a[i]` works, but
  `a[n]` with `n: i32` doesn't.
- Writing `unit` or `void`. The unit type is `tuple()`.
- Expecting `x as bool`. Write `x != 0`.
- Expecting `&local`. Only memory behind a pointer has an address.
- Forgetting to label struct constructor arguments, or to give type arguments
  to a generic struct: `Box(i32)(value: 1)`, not `Box(value: 1)`.
- Writing `&= |= <<=`. Write `a = a & b`.
- Naming a `pub` item `memory`.
