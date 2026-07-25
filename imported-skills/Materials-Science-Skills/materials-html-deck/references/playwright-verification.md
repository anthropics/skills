# Strict Playwright Verification

Attribution: copied and trimmed from
`huashu-design/references/verification.md`.

Every generated deck must pass browser verification before delivery. The
verifier opens each `slides/*.html` file directly and checks:

- no `pageerror` events,
- no browser console errors,
- visible body with non-empty content,
- screenshot written for every slide,
- no missing local media referenced by `src` or `href`.

Run:

```powershell
node scripts/verify_deck_html.mjs --html-dir output/final_deck_html --screenshots output/final_deck_html/screenshots
```

If Playwright is unavailable, the user-facing build command must fail and print
install instructions. CI may skip browser-dependent tests only when the test
code explicitly detects missing Playwright.
