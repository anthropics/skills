---
name: fp-go
description: >
  Use this skill whenever writing, reviewing, or refactoring Go code that uses
  the fp-go library (github.com/IBM/fp-go/v2). Trigger on any mention of fp-go,
  functional programming in Go, monads in Go, Option/Either/Result types in Go,
  IOResult, ReaderIOResult, data-last composition, Pipe/Flow, or do-notation with
  Bind/ApS in Go. Also trigger when the user wants to convert idiomatic Go
  error handling into functional pipelines, or asks about optics (lens, prism,
  traversal) in Go.
---

# fp-go v2 — Functional Programming for Go

## Critical Rules for Code Generation

1. **Import path is v2**: always `github.com/IBM/fp-go/v2/...`, never `github.com/IBM/fp-go/...` (that is v1).
2. **Data-last**: all operations return a function waiting for data. Write `option.Map(f)(value)`, never `option.Map(value, f)`.
3. **Non-inferrable type parameters come first**: `Map[B, A]`, `Ap[B, A]`, `Chain[B, A]`. The compiler infers trailing params from arguments; leading params often need explicit annotation.
4. **Prefer `Result` over `Either`** when the error type is Go's `error`. `Result[A]` is `Either[error, A]`. Same for `ioresult` over `ioeither`, `readerioresult` over `readerioeither`.
5. **IO values are lazy**: `IO[A]` is `func() A`. They describe a computation — you must call `()` to execute. Don't forget the trailing `()`.
6. **Prefer point-free style**: compose with `F.Flow` and `F.Pipe` instead of writing inline anonymous functions. If a transformation can be expressed as a composition of named functions, it should be. Point-free pipelines are idiomatic fp-go.
## Overview

`fp-go` (import path `github.com/IBM/fp-go/v2`) brings type-safe functional programming to Go using generics. Every monad follows a **consistent interface**: once you know the pattern in one monad, it transfers to all others.

All functions use the **data-last** principle: the data being transformed is always the last argument, enabling partial application and pipeline composition.

## Core Types

| Type | Package | Represents |
|------|---------|------------|
| `Option[A]` | `option` | A value that may or may not be present (replaces nil) |
| `Either[E, A]` | `either` | A value that is either a left error `E` or a right success `A` |
| `Result[A]` | `result` | `Either[error, A]` — **recommended default** for error handling |
| `IO[A]` | `io` | A lazy computation that produces `A` (possibly with side effects) |
| `IOResult[A]` | `ioresult` | `IO[Result[A]]` — lazy computation that can fail |
| `ReaderIOResult[A]` | `context/readerioresult` | `func(context.Context) IOResult[A]` — context-aware IO with errors |
| `Effect[C, A]` | `effect` | `func(C) ReaderIOResult[A]` — **typed dependency injection** + IO + errors; recommended for services |

### Idiomatic Packages (high-performance, tuple-based)

The `idiomatic/` packages use Go-native tuples instead of struct wrappers, offering 2–10× better performance and zero allocations. Use them in hot paths; use standard packages when you need the richer API surface.

- `idiomatic/option` — `(A, bool)` tuples
- `idiomatic/result` — `(A, error)` tuples
- `idiomatic/ioresult` — `func() (A, error)`
- `idiomatic/context/readerresult` — `func(context.Context) (A, error)`

## Standard Operations

Every monad exports these operations (PascalCase for exported Go names):

| fp-go | fp-ts / Haskell | Description |
|-------|----------------|-------------|
| `Of` | `of` / `pure` | Lift a pure value into the monad |
| `Map` | `map` / `fmap` | Transform the value inside without changing the context |
| `Chain` | `chain` / `>>=` | Sequence a computation that itself returns a monadic value |
| `Ap` | `ap` / `<*>` | Apply a wrapped function to a wrapped value |
| `Fold` | `fold` / `either` | Eliminate the context — handle every case and extract a plain value |
| `GetOrElse` | `getOrElse` / `fromMaybe` | Extract the value or use a default (Option/Result) |
| `Filter` | `filter` / `mfilter` | Keep only values satisfying a predicate |
| `Flatten` | `flatten` / `join` | Remove one level of nesting (`M[M[A]]` → `M[A]`) |
| `ChainFirst` | `chainFirst` / `>>` | Sequence for side effects; keeps the original value |
| `Alt` | `alt` / `<|>` | Provide an alternative when the first computation fails |
| `FromPredicate` | `fromPredicate` / `guard` | Build a monadic value from a predicate |
| `Sequence` | `sequence` | Turn `[]M[A]` into `M[[]A]` |
| `Traverse` | `traverse` | Map and sequence in one step |

Curried (composable) vs. monadic (direct) form:

```go
// Curried — data last, returns a transformer function
option.Map(strings.ToUpper)              // func(Option[string]) Option[string]

// Monadic — data first, immediate execution
option.MonadMap(option.Some("hello"), strings.ToUpper)
```

Use curried form for pipelines; use `Monad*` form when you already have all arguments.

## Key Type Aliases (defined per monad)

```go
// A Kleisli arrow: a function from A to a monadic B
type Kleisli[A, B any] = func(A) M[B]

// An operator: transforms one monadic value into another
type Operator[A, B any] = func(M[A]) M[B]
```

`Chain` takes a `Kleisli`, `Map` returns an `Operator`. The naming is consistent across all monads.

## Function Composition with Flow and Pipe (Point-Free Style)

fp-go is designed for **point-free** programming: compose named functions with `Flow` and `Pipe` rather than writing inline anonymous functions. This makes pipelines more readable and eliminates intermediate variable naming.

```go
import (
    F  "github.com/IBM/fp-go/v2/function"
    S  "github.com/IBM/fp-go/v2/string"
    LZ "github.com/IBM/fp-go/v2/lazy"
)

// ✅ GOOD: point-free — compose named functions, no lambda noise
pipeline := F.Flow3(
    R.Eitherize1(strconv.Atoi),
    R.Map(N.Mul(2)),
    R.GetOrElse(F.Constant(0)),
)

// ❌ AVOID: wrapping in unnecessary anonymous functions
pipeline := F.Flow3(
    func(s string) R.Result[int] { return R.Eitherize1(strconv.Atoi)(s) },
    func(r R.Result[int]) R.Result[int] { return R.Map(func(n int) int { return n * 2 })(r) },
    func(r R.Result[int]) int { return R.GetOrElse(func() int { return 0 })(r) },
)
```

The data-last design means every fp-go operation already returns a function — so you almost never need to wrap them in a lambda. When you do need to adapt arguments, use `F.Flow2` to compose:

```go
// Point-free: compose a lens getter with a Kleisli arrow
RIO.Bind(configLens.Set, F.Flow2(userLens.Get, fetchConfigForUser))

// Instead of:
RIO.Bind(configLens.Set, func(s Pipeline) RIO.ReaderIOResult[Config] {
    return fetchConfigForUser(userLens.Get(s))
})
```

Two forms:

```go
// Flow: compose functions left-to-right, returns a new function
transform := F.Flow3(
    option.Map(strings.TrimSpace),
    option.Filter(S.IsNonEmpty),
    option.GetOrElse(LZ.Of("default")),
)
result := transform(option.Some("  hello  ")) // "hello"

// Pipe: apply a value through a pipeline immediately
result := F.Pipe3(
    option.Some("  hello  "),
    option.Map(strings.TrimSpace),
    option.Filter(S.IsNonEmpty),
    option.GetOrElse(LZ.Of("default")),
)
```

`Pipe1`–`Pipe20` and `Flow1`–`Flow20` are available (the number = number of transformation steps).

## Lifting Go Functions into Monadic Context

| Helper | Lifts |
|--------|-------|
| `Eitherize1`..`EitherizeN` | `func(args...) (B, error)` → `func(args...) Result[B]` — **primary bridge from Go to fp-go** |
| `ChainEitherK` | `func(A) (B, error)` → works inside the monad |
| `ChainOptionK` | `func(A) Option[B]` → works inside the monad |
| `ChainFirstIOK` | `func(A) IO[B]` for side effects, keeps original value |
| `FromPredicate` | `func(A) bool` + error builder → `func(A) Result[A]` |

## Examples

### Option — nullable values without nil

```go
import (
    O  "github.com/IBM/fp-go/v2/option"
    F  "github.com/IBM/fp-go/v2/function"
    S  "github.com/IBM/fp-go/v2/string"
    "strconv"
)

parseAndDouble := F.Flow2(
    O.FromPredicate(S.IsNonEmpty),
    O.Chain(func(s string) O.Option[int] {
        n, err := strconv.Atoi(s)
        if err != nil {
            return O.None[int]()
        }
        return O.Some(n * 2)
    }),
)

parseAndDouble("21")  // Some(42)
parseAndDouble("")    // None
parseAndDouble("abc") // None
```

### Result — error handling without if-err boilerplate

```go
import (
    R  "github.com/IBM/fp-go/v2/result"
    F  "github.com/IBM/fp-go/v2/function"
    "strconv"
    "errors"
)

parse := R.Eitherize1(strconv.Atoi)  // lifts (int, error) → Result[int]

validate := func(n int) R.Result[int] {
    if n < 0 {
        return R.Error[int](errors.New("must be non-negative"))
    }
    return R.Of(n)
}

pipeline := F.Flow2(parse, R.Chain(validate))

pipeline("42")   // Ok(42)
pipeline("-1")   // Error("must be non-negative")
pipeline("abc")  // Error(strconv parse error)
```

### IOResult — lazy IO with error handling

```go
import (
    IOE "github.com/IBM/fp-go/v2/ioresult"
    F   "github.com/IBM/fp-go/v2/function"
    J   "github.com/IBM/fp-go/v2/json"
    "os"
)

readConfig := F.Flow2(
    IOE.Eitherize1(os.ReadFile),           // func(string) IOResult[[]byte]
    IOE.ChainEitherK(J.Unmarshal[Config]), // parse JSON, propagate errors
)

result := readConfig("config.json")() // execute lazily — note the trailing ()
```

### ReaderIOResult — context-aware pipelines (recommended for services)

```go
import (
    RIO "github.com/IBM/fp-go/v2/context/readerioresult"
    F   "github.com/IBM/fp-go/v2/function"
    "context"
)

// type ReaderIOResult[A any] = func(context.Context) func() result.Result[A]

fetchUser := func(id int) RIO.ReaderIOResult[User] {
    return func(ctx context.Context) func() result.Result[User] {
        return func() result.Result[User] {
            // perform IO here
        }
    }
}

pipeline := F.Pipe3(
    fetchUser(42),
    RIO.ChainEitherK(validateUser),    // lift pure (User, error) function
    RIO.Map(enrichUser),               // lift pure User → User function
    RIO.ChainFirstIOK(IO.Logf[User]("Fetched: %v")), // side-effect logging
)

user, err := pipeline(ctx)() // provide context once, execute
```

### Effect — typed dependency injection (recommended for testable services)

`Effect[C, A]` adds a **typed dependency parameter** `C` on top of `ReaderIOResult`. While `context/readerioresult` hardcodes `context.Context` as the environment, `Effect` lets you define a custom dependencies struct — making dependencies explicit, compile-time checked, and trivially mockable in tests.

Use `Effect` when your service has dependencies beyond `context.Context` (database connections, HTTP clients, config, loggers). It is the **recommended top-level monad for production service code**.

```go
import (
    EF "github.com/IBM/fp-go/v2/effect"
    F  "github.com/IBM/fp-go/v2/function"
    L  "github.com/IBM/fp-go/v2/optics/lens"
)

// 1. Define your dependencies as a struct
type Deps struct {
    DB     DBClient
    Logger Logger
    Config AppConfig
}

// 2. Write effects that declare exactly what they need
// Effect[Deps, User] = func(Deps) ReaderIOResult[User]
fetchUser := func(id int) EF.Effect[Deps, User] {
    return EF.Asks(func(deps Deps) EF.ReaderIOResult[User] {
        // deps.DB is available here — compile-time checked
        return queryUser(deps.DB, id)
    })
}

enrichWithConfig := func(user User) EF.Effect[Deps, EnrichedUser] {
    return EF.Asks(func(deps Deps) EF.ReaderIOResult[EnrichedUser] {
        return RIO.Of(applyConfig(user, deps.Config))
    })
}

// 3. Compose effects — same Map/Chain/Bind/ApS API as every other monad
pipeline := F.Pipe2(
    fetchUser(42),
    EF.Chain(enrichWithConfig),
    EF.Map(func(u EnrichedUser) string { return u.DisplayName }),
)

// 4. Provide dependencies once at the edge, then run
result := EF.Provide(Deps{
    DB:     realDB,
    Logger: zapLogger,
    Config: loadedConfig,
})(pipeline) // returns ReaderIOResult[string]

value := result(ctx)() // provide context, execute
```

**Why Effect over `ReaderIOResult`:** dependencies are typed (compiler catches missing deps), each function's signature declares what it needs (`Effect[Deps, A]`), testability is trivial (swap `Deps{DB: mockDB}`), and `EF.Local`/`EF.Provide` narrow or eliminate deps for subsystems.

**Lifting into Effect:** `EF.Ask[Deps]()` reads the full struct, `EF.Asks(f)` reads deps and produces a `ReaderIOResult`, `EF.Of(a)`/`EF.Succeed(a)` lift pure values, `EF.Fail(err)` lifts errors, `EF.Eitherize1(f)` lifts `func(A) (B, error)`, `EF.FromResult(r)` lifts a `Result`, and `EF.RunSync(fa)` executes synchronously.

### Traversal — process slices monadically

```go
import (
    A   "github.com/IBM/fp-go/v2/array"
    RIO "github.com/IBM/fp-go/v2/context/readerioresult"
    F   "github.com/IBM/fp-go/v2/function"
)

// Fetch all users, stop on first error
fetchAll := F.Pipe1(
    A.MakeBy(10, userID),
    RIO.TraverseArray(fetchUser),  // []ReaderIOResult[User] → ReaderIOResult[[]User]
)
```

## When to Use Which Monad

| Situation | Use |
|-----------|-----|
| Value that might be absent | `Option[A]` |
| Operation that can fail with custom error type | `Either[E, A]` |
| Operation that can fail with `error` | `Result[A]` |
| Lazy IO, side effects | `IO[A]` |
| IO that can fail | `IOResult[A]` |
| IO + context (cancellation, deadlines) | `ReaderIOResult[A]` from `context/readerioresult` |
| IO + context + typed dependencies (services, DI) | **`Effect[C, A]`** — recommended for production services |
| High-performance services | Idiomatic packages in `idiomatic/` |

Escalation path: `Option` → `Result` → `IOResult` → `ReaderIOResult` → **`Effect`**. Start with the simplest monad that covers your needs. For real-world services with database clients, HTTP clients, or config — go straight to `Effect`; it provides compile-time dependency safety that `ReaderIOResult` with raw `context.Context` cannot.

## Do-Notation: Accumulating State with `Bind` and `ApS`

When a pipeline needs to carry **multiple intermediate results** forward, `Chain`/`Map` becomes unwieldy because each step only threads one value. Do-notation solves this by accumulating results into a growing struct at each step.

Every monad that supports do-notation exports the same family. Examples below use `context/readerioresult` (`RIO`), but the identical API is available in `result`, `option`, `ioresult`, `readerioresult`, and others.

### The Function Family

| Function | Kind | What it does |
|----------|------|-------------|
| `Do(empty S)` | — | Lift an empty struct into the monad; starting point |
| `BindTo(setter)` | monadic | Convert an existing `M[T]` into `M[S]`; alternative start |
| `Bind(setter, f)` | monadic | Add a result; `f` receives the **current state** and returns `M[T]` |
| `ApS(setter, fa)` | applicative | Add a result; `fa` is **independent** of the current state |
| `Let(setter, f)` | pure | Add a value computed by a **pure function** of the state |
| `LetTo(setter, value)` | pure | Add a **constant** value |

Lens variants (`BindL`, `ApSL`, `LetL`, `LetToL`) accept a `Lens[S, T]` instead of a manual setter.

### `Bind` — Sequential, Dependent Steps

`Bind` sequences two monadic computations. `f` receives the **full accumulated state** so it can read anything gathered so far. Errors short-circuit.

```go
import (
    RIO "github.com/IBM/fp-go/v2/context/readerioresult"
    F   "github.com/IBM/fp-go/v2/function"
    L   "github.com/IBM/fp-go/v2/optics/lens"
    "context"
)

type Pipeline struct {
    User   User
    Config Config
    Posts  []Post
}

var (
    userLens   = L.MakeLens(func(s Pipeline) User   { return s.User },   func(s Pipeline, u User)   Pipeline { s.User = u; return s })
    configLens = L.MakeLens(func(s Pipeline) Config { return s.Config }, func(s Pipeline, c Config) Pipeline { s.Config = c; return s })
    postsLens  = L.MakeLens(func(s Pipeline) []Post { return s.Posts },  func(s Pipeline, p []Post) Pipeline { s.Posts = p; return s })
)

result := F.Pipe3(
    RIO.Do(Pipeline{}),
    RIO.Bind(userLens.Set,   func(_ Pipeline) RIO.ReaderIOResult[User] { return fetchUser(42) }),
    RIO.Bind(configLens.Set, F.Flow2(userLens.Get, fetchConfigForUser)),
    RIO.Bind(postsLens.Set,  F.Flow2(userLens.Get, fetchPostsForUser)),
)

pipeline, err := result(context.Background())()
```

The setter signature is `func(T) func(S1) S2`. `lens.Set` already has this shape. `F.Flow2(lens.Get, f)` composes the field getter with any Kleisli arrow point-free.

### `ApS` — Independent, Applicative Steps

`ApS` uses **applicative** semantics: `fa` is evaluated without access to state. Use when steps have no dependency on each other.

```go
// Using same lens pattern as Bind — but steps are independent
result := F.Pipe2(
    RIO.Do(Summary{}),
    RIO.ApS(userLens.Set,    fetchUser(42)),     // no access to state
    RIO.ApS(weatherLens.Set, fetchWeather("NYC")), // no access to state
)
```

**Key difference:**

| | `Bind(setter, f)` | `ApS(setter, fa)` |
|-|---|---|
| Second argument | `func(S1) M[T]` — function of state | `M[T]` — fixed monadic value |
| Can read prior state? | Yes | No |
| Semantics | Monadic (sequential) | Applicative (independent) |

### `Let`, `LetTo`, `BindTo`

- `Let(setter, f)` — add a value from a **pure function** of state (no monad, cannot fail)
- `LetTo(setter, value)` — add a **constant**
- `BindTo(project)` — start from an existing `M[T]` instead of `Do(empty)`

### Lifted Variants for Mixed Monads

`Bind*K` helpers lift simpler computations into the do-chain: `BindResultK`/`BindEitherK` for `func(S1) (T, error)`, `BindIOResultK` for `func(S1) func() (T, error)`, `BindIOK` for `func(S1) func() T`, `BindReaderK` for `func(S1) func(ctx) T`.

### Do-Notation Decision Guide

```
Does the new step need to read prior accumulated state?
    YES  →  Bind   (monadic, sequential; f receives current S)
    NO   →  ApS    (applicative, independent; fa is a fixed M[T])

Is the new value derived purely from state, with no monad?
    YES  →  Let    (pure function of S)

Is the new value a compile-time or runtime constant?
    YES  →  LetTo

Starting from an existing M[T] rather than an empty struct?
    YES  →  BindTo
```

### Complete Example — `result` Monad with Lenses

```go
import (
    R    "github.com/IBM/fp-go/v2/result"
    F    "github.com/IBM/fp-go/v2/function"
    L    "github.com/IBM/fp-go/v2/optics/lens"
    N    "github.com/IBM/fp-go/v2/number"
    "strconv"
)

type Parsed struct {
    Raw    string
    Number int
    Double int
}

var (
    rawLens    = L.MakeLens(
        func(s Parsed) string { return s.Raw },
        func(s Parsed, v string) Parsed { s.Raw = v; return s },
    )
    numberLens = L.MakeLens(
        func(s Parsed) int { return s.Number },
        func(s Parsed, v int) Parsed { s.Number = v; return s },
    )
    doubleLens = L.MakeLens(
        func(s Parsed) int { return s.Double },
        func(s Parsed, v int) Parsed { s.Double = v; return s },
    )
)

var atoi = R.Eitherize1(strconv.Atoi) // func(string) Result[int]

parse := func(input string) R.Result[Parsed] {
    return F.Pipe3(
        R.Do(Parsed{}),
        R.LetTo(rawLens.Set, input),
        R.Bind(numberLens.Set, F.Flow2(rawLens.Get, atoi)),
        R.Let(doubleLens.Set, F.Flow2(numberLens.Get, N.Mul(2))),
    )
}

parse("21")  // Ok(Parsed{Raw:"21", Number:21, Double:42})
parse("abc") // Error(strconv parse error)
```

## Common Mistakes

| Mistake | Fix |
|---------|-----|
| `import "github.com/IBM/fp-go/result"` | Use v2: `"github.com/IBM/fp-go/v2/result"` |
| `option.Map(myOption, f)` | Data-last: `option.Map(f)(myOption)` |
| `either.Map[A, B](f)` | Non-inferrable first: `either.Map[B](f)` or let compiler infer |
| Using `ioeither` with `error` | Use `ioresult` instead; reserve `ioeither` for custom error types |
| `readConfig := IOE.Eitherize1(os.ReadFile)` then using result directly | `IOResult` is lazy — call `readConfig("path")()` with trailing `()` |
| Writing inline setter lambdas for Do-notation | Use `L.MakeLens` + `lens.Set`; the signature already matches |
| Using `Bind` when steps are independent | Use `ApS` for independent steps — clearer intent, potentially concurrent |
| Using `context/readerioresult` with deps stuffed into `context.Context` | Use `effect.Effect[Deps, A]` — typed deps are compile-time checked and testable |
| Wrapping fp-go operations in anonymous functions | Go point-free: `option.Filter(S.IsNonEmpty)` not `option.Filter(func(s string) bool { return s != "" })`, `option.GetOrElse(LZ.Of("x"))` not `option.GetOrElse(func() string { return "x" })` |

Requires Go 1.24+ for generic type alias support.
