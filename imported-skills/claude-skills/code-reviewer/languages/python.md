---
language: python
extensions: [".py"]
---

# Python — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Python-specific rules and idioms.

---

## PR Analyzer — Python Risk Signals

- `print()` statements left in production code
- `# noqa` and `# type: ignore` comments — verify they are justified
- `eval()` / `exec()` with any user-controlled input
- `pickle` used to deserialize untrusted data
- Hardcoded credentials or tokens in source

---

## Code Quality — Python Checks

- Bare `except:` or `except Exception:` swallowing silently
- Mutable default arguments (`def foo(items=[])`) — shared across calls
- `import *` — pollutes namespace and hides dependencies
- Missing type hints on public functions and methods
- `assert` used for runtime validation — stripped by `-O` flag

---

## Security

- Flag `eval()` / `exec()` with any user-controlled input
- Flag `pickle.loads()` on untrusted data — use `json` or `msgpack`
- Flag `subprocess` calls with `shell=True` and user input
- Flag `flask.render_template_string()` with user data (SSTI)
- Flag `SECRET_KEY` / `DEBUG = True` committed to source

---

## Async

- Flag `asyncio.get_event_loop().run_until_complete()` inside an already-running loop
- Flag mixing `threading` and `asyncio` without a clear bridge (`run_in_executor`)
- Flag CPU-bound work inside an `async def` without offloading to `ProcessPoolExecutor`
- Flag `time.sleep()` inside async functions — use `await asyncio.sleep()`

---

## Resource Management

- Flag `open()` not used as a context manager (`with open(...) as f`)
- Flag `requests.Session` created per-request instead of shared/reused
- Flag database connections not closed or returned to a pool on all paths
- Flag large files read entirely into memory with `.read()` — prefer streaming / chunked reads

---

## Exception Handling

- Flag bare `except:` — catches `BaseException` including `KeyboardInterrupt` and `SystemExit`
- Flag `except Exception: pass` — silently swallows errors
- Flag re-raising with `raise e` instead of `raise` — loses the original traceback
- Flag `except` clause too broad when the `try` block covers multiple operations with different failure modes — split them

---

## Performance

- Flag `+` string concatenation in loops — use `"".join()`
- Flag repeated `re.compile()` inside a loop — compile once at module level
- Flag `list.append()` in a loop where a list comprehension would be more efficient
- Flag `in` membership tests on `list` where the collection is large — use `set`
- Flag loading entire large files into memory — prefer streaming or chunked reads

---

## Idioms and Best Practices

### Type Safety
- All public functions and methods should have type annotations
- Prefer `X | None` (Python 3.10+) over `Optional[X]`
- Use `TypedDict` or `dataclass` over plain `dict` for structured data

### Modern Python (3.10+)
- Prefer `match` statements over long `if/elif` chains
- Prefer `dataclass` or `NamedTuple` over plain classes for data carriers
- Prefer `pathlib.Path` over `os.path` for file operations
- Prefer f-strings over `.format()` or `%` formatting

### None Safety
- Prefer explicit `if x is None` over falsy checks when `0` or `""` are valid values
- Flag functions returning `None` implicitly — make it explicit or raise
