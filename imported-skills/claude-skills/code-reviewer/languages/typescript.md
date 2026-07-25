---
language: typescript
extensions: [".ts", ".tsx", ".js", ".jsx", ".mjs"]
---

# TypeScript / JavaScript — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only TypeScript/JavaScript-specific rules and idioms.

---

## PR Analyzer — TypeScript / JavaScript Risk Signals

- `console.log` / `debugger` statements left in production code
- `// eslint-disable` comments — verify they are justified
- `any` type annotations — require explicit justification
- `@ts-ignore` / `@ts-expect-error` — verify they are justified
- `eval()` with any dynamic or user-controlled input
- Hardcoded API keys or tokens in source

---

## Code Quality — TypeScript / JavaScript Checks

- `any` used broadly instead of proper typing
- Non-null assertion (`!`) used without justification
- `var` declarations — prefer `const` / `let`
- Missing `await` on async function calls
- Floating promises (no `.catch()` and no `await`)
- `==` used instead of `===`

---

## Security

- Flag `innerHTML`, `outerHTML`, `document.write()` with user-controlled data — use `textContent` or a sanitizer
- Flag `dangerouslySetInnerHTML` in React without a sanitizer
- Flag `eval()` / `new Function()` with dynamic input
- Flag JWT decoded without signature verification
- Flag missing `httpOnly` / `secure` flags on cookies

---

## Async / Promises

- Flag floating promises — async calls not `await`-ed and without `.catch()`
- Flag `Promise.all()` where `Promise.allSettled()` is safer (one failure should not cancel siblings)
- Flag `async` functions inside `forEach` — `forEach` does not await; use `for...of` or `Promise.all()`
- Flag unhandled promise rejection (no global `unhandledRejection` handler in Node.js services)

---

## Resource Management

- Flag `fs.createReadStream` / `fs.createWriteStream` with no `close` or `destroy` on error
- Flag `EventEmitter` listeners added in a loop without removal — memory leak
- Flag `setInterval` / `setTimeout` handles not cleared when the owning component unmounts or exits
- Flag database clients / pools not released after use in Node.js

---

## Exception Handling

- Flag `catch (e) {}` (empty catch) — swallowed error
- Flag `catch (e)` where `e` is used as `any` without narrowing — type the error properly
- Flag `Promise` rejection not handled — `.catch()` or `try/await/catch` required
- Flag re-throwing a new `Error` without wrapping the original — loses stack context
- Use `Error` subclasses for domain errors rather than plain strings or object literals

---

## Performance

- Flag `Array.prototype.find` / `filter` / `map` chained multiple times over the same array — combine into one pass
- Flag DOM queries (`document.querySelector`) inside loops — cache the result
- Flag `JSON.parse` / `JSON.stringify` in a hot path on large objects — consider streaming or partial parsing
- Flag `async` functions called sequentially in a loop where `Promise.all()` would parallelize them

---

## Idioms and Best Practices

### Type Safety (TypeScript)
- Prefer `unknown` over `any` for truly unknown values — forces a type guard before use
- Prefer type narrowing (`typeof`, `instanceof`, discriminated unions) over casting
- Enable `strict` mode in `tsconfig.json`
- Prefer `interface` for object shapes that may be extended; `type` for unions and aliases

### Modern JavaScript / TypeScript
- Prefer `const` by default; `let` only when reassignment is needed
- Prefer optional chaining (`?.`) and nullish coalescing (`??`) over manual null guards
- Prefer `structuredClone()` over manual deep-copy patterns
- Prefer named exports over default exports for better refactoring support

### Null / Undefined Safety
- Distinguish between `null` (intentional absence) and `undefined` (not set) — be consistent
- Flag `== null` checks that accidentally include `undefined` when only one is intended
