# Toolchain

Default generation uses Node.js:

```powershell
node scripts/build_deck.mjs output/ppt_outline_cn.json output/final_deck_html --style assertion-evidence
```

The build command writes HTML files, invokes `verify_deck_html.mjs`, and stops
if strict browser verification fails.

Required runtime:

- Node.js
- Playwright for Chromium rendering and screenshots
- Python only for optional figure extraction helpers

If Playwright is missing, do not silently deliver. Print install instructions
and stop.
