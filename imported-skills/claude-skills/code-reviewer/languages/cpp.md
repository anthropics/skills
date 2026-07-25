---
language: cpp
extensions: [".cpp", ".cc", ".cxx", ".hpp", ".hh", ".hxx"]
---

# C++ — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only C++-specific rules and idioms.

---

## PR Analyzer — C++ Risk Signals

- Raw `new` / `delete` outside of smart pointer wrappers
- `reinterpret_cast` — almost always a red flag; require justification
- Disabled compiler warnings (`#pragma warning(disable:...)`, `-w`)
- `// TODO` / `// FIXME` near ownership or lifetime code
- Hardcoded credentials or keys in source
- Use of deprecated C-style functions: `strcpy`, `sprintf`, `gets`

---

## Code Quality — C++ Checks

- Raw owning pointers (`T*`) used where `unique_ptr` / `shared_ptr` would express ownership
- `shared_ptr` overused where `unique_ptr` suffices — implies shared ownership unnecessarily
- `std::endl` used in hot paths — flushes the buffer every call; prefer `'\n'`
- Implicit conversions between signed and unsigned integers
- Virtual destructor missing on base classes with virtual methods
- `catch (...)` swallowing all exceptions without logging or re-throwing

---

## Security

- Flag `reinterpret_cast` on user-controlled data — potential type confusion
- Flag raw array indexing without bounds check — use `.at()` or assert bounds
- Flag `std::string` data passed to C APIs without null-termination guarantee — use `.c_str()`
- Flag hardcoded buffer sizes — derive from `sizeof` or use `std::array<T, N>`
- Flag `sscanf` / `sprintf` — use `std::istringstream` or `std::format` (C++20)
- Flag user-controlled data used as a format string

---

## Async / Concurrency

- Flag `std::shared_ptr` accessed from multiple threads — the pointer itself is not thread-safe for write; use `std::atomic<std::shared_ptr<T>>` (C++20) or external locking
- Flag `std::vector` / `std::map` mutated from multiple threads without a mutex
- Flag `std::mutex` locked twice in the same thread without `std::recursive_mutex` — deadlock
- Flag detached threads (`std::thread::detach`) with no lifetime coordination
- Flag `volatile` used instead of `std::atomic` for inter-thread communication

---

## Resource Management

- Flag raw `new` returning an owning pointer — wrap immediately in `std::make_unique` or `std::make_shared`
- Flag `delete` called manually outside of a destructor or smart pointer — ownership confusion
- Flag RAII violations — resources acquired in constructor but not released via destructor
- Flag `std::ifstream` / `std::ofstream` not checked for open failure before use
- Flag exceptions thrown from destructors — causes `std::terminate` if thrown during stack unwinding

---

## Exception Handling

- Flag `catch (...)` that swallows exceptions without logging or re-throwing
- Flag exceptions thrown from destructors — wrap in `try/catch` inside the destructor
- Flag `noexcept` on functions that can actually throw — causes `std::terminate`
- Flag exception specifications (`throw(...)`) — deprecated since C++11, removed in C++17
- Flag using exceptions for control flow in performance-critical paths

---

## Performance

- Flag pass-by-value for non-trivial types where pass-by-const-reference suffices
- Flag `std::vector::push_back` in a loop without `reserve` when size is known — repeated reallocations
- Flag `std::map` used where `std::unordered_map` would give O(1) lookup
- Flag `std::endl` in loops — prefer `'\n'` to avoid repeated buffer flushes
- Flag unnecessary copies from missing `std::move` on local temporaries being returned or passed

---

## Idioms and Best Practices

### Ownership and Lifetime
- Prefer `std::unique_ptr` for sole ownership, `std::shared_ptr` only for shared ownership
- Prefer `std::make_unique` / `std::make_shared` over `new` — exception-safe
- Use `std::weak_ptr` to break `shared_ptr` cycles
- Never use raw owning pointers in new code — they are for non-owning observation only

### Modern C++ (17/20)
- Prefer `std::optional<T>` over sentinel values or nullable pointers for optional returns
- Prefer `std::variant` over tagged unions
- Prefer `std::string_view` over `const std::string&` for read-only string parameters
- Prefer range-based `for` loops over index loops where the index isn't needed
- Prefer `if constexpr` over `#ifdef` for compile-time branching

### Type Safety
- Prefer `static_cast` over C-style casts — explicit and auditable
- Avoid `reinterpret_cast` except in low-level I/O or FFI code with a comment
- Use `enum class` over plain `enum` to avoid implicit integer conversions
