---
language: ruby
extensions: [".rb", ".rake", ".gemspec", ".ru"]
---

# Ruby — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Ruby-specific rules and idioms.

---

## PR Analyzer — Ruby Risk Signals

- `puts` / `p` / `pp` debug statements left in production code
- `# rubocop:disable` comments — verify they are justified
- `eval` / `instance_eval` / `class_eval` with user-controlled input
- Hardcoded credentials, tokens, or `SECRET_KEY_BASE` in source
- `binding.pry` / `byebug` / `debugger` left in code

---

## Code Quality — Ruby Checks

- Methods longer than 15 lines — Ruby idioms favor very small methods
- Classes with more than 10 public methods — possible god object
- `rescue Exception` — catches `SignalException` and `SystemExit`; use `rescue StandardError` or more specific types
- `method_missing` implemented without `respond_to_missing?`
- Deeply nested blocks (>3 levels) — extract to methods
- String interpolation used where a symbol would suffice (hash keys, etc.)

---

## Security

- Flag `eval` / `instance_eval` with user-controlled strings — remote code execution
- Flag `system()` / `exec()` / backtick calls with user-controlled input — shell injection
- Flag `YAML.load` on untrusted data — use `YAML.safe_load`
- Flag `Marshal.load` on untrusted data — arbitrary code execution
- Flag raw SQL string interpolation in ActiveRecord — use parameterized queries (`where("name = ?", name)`)
- Flag `params` passed directly to `redirect_to` without validation — open redirect
- Flag `render inline:` with user data — XSS via ERB
- Flag missing `strong_parameters` in Rails controllers — mass assignment vulnerability

---

## Async / Concurrency

- Flag shared mutable state accessed from multiple threads without a `Mutex`
- Flag `Thread.new` without storing the thread reference — exceptions are silently swallowed
- Flag `sleep` used as a synchronization mechanism in threaded code
- Flag `@@class_variables` mutated in multi-threaded contexts — not thread-safe
- Flag Sidekiq / ActiveJob workers that are not idempotent — jobs can be retried

---

## Resource Management

- Flag `File.open` without a block form — the block form guarantees `close`
- Flag database connections or HTTP clients not released in `ensure` blocks
- Flag `ActiveRecord` queries inside loops — N+1 pattern; use `includes` / `preload` / `eager_load`
- Flag `ObjectSpace` usage in production — memory and performance impact

---

## Exception Handling

- Flag `rescue Exception` — use `rescue StandardError` or a specific exception class
- Flag empty `rescue` blocks — swallowed errors
- Flag `rescue` used for control flow (e.g. rescuing `ActiveRecord::RecordNotFound` instead of using `find_by`)
- Flag re-raising with `raise e` instead of bare `raise` — loses the original backtrace
- Flag `ensure` blocks that can raise — masks the original exception

---

## Performance

- Flag N+1 ActiveRecord queries — use `includes`, `preload`, or `eager_load`
- Flag `Array#each` with string concatenation — use `map` + `join`
- Flag `select` + `map` that could be a single `filter_map`
- Flag `.count` on an ActiveRecord relation inside a view or loop — triggers a query each time
- Flag `require` inside a method body — constant overhead on every call
- Flag `Hash#merge` in a loop — use `merge!` or `each_with_object`

---

## Idioms and Best Practices

### Ruby Style
- Prefer `map` / `select` / `reject` / `reduce` over manual `each` + accumulator
- Prefer `&method(:name)` over `{ |x| some_method(x) }` for method reference blocks
- Prefer `freeze` on string constants to avoid repeated object allocation
- Use `attr_reader` / `attr_writer` / `attr_accessor` instead of manual getter/setter methods
- Prefer `Symbol#to_proc` (`&:method_name`) for simple single-method blocks

### Rails-Specific
- Keep controllers thin — logic belongs in service objects, models, or concerns
- Use `before_action` for authentication/authorization checks — never inline
- Prefer `find_by` over `where(...).first` — more intent-revealing
- Flag `after_commit` callbacks with side effects that should be in a service object
- Prefer `respond_to` blocks over separate controller actions for format variants

### Modern Ruby (3.x)
- Prefer pattern matching (`case/in`) for complex data destructuring
- Use numbered block parameters (`_1`, `_2`) only for very short, obvious blocks
- Prefer `Data.define` for simple immutable value objects (Ruby 3.2+)
