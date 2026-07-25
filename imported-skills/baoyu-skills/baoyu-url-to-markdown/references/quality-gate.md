# Quality Gate & Recovery

Headless Chrome can silently return low-quality content — layout shells, login walls, or framework payloads — without the CLI returning a non-zero exit code. Read this after every headless run so you can catch and recover from those cases.

## Checks the Agent Must Run

1. Confirm the markdown title matches the target page, not a generic site shell
2. Confirm the body contains the expected article/page content, not just navigation, footer, or a generic error
3. Watch for obvious failure signs:
   - `Application error`
   - `This page could not be found`
   - Login, signup, subscribe, or verification shells
   - Extremely short markdown for a page that should be long-form
   - Raw framework payloads or mostly boilerplate content
4. Do NOT accept a run as successful just because the CLI exited `0`

**Tip**: run with `--format json` to get structured signals including `status`, `login.state`, and `interaction`. `"status": "needs_interaction"` means the page requires manual interaction.

## Recovery Workflow

1. Start headless (default) unless there is already a clear reason to use interaction mode
2. Review markdown quality immediately after the run
3. If the content is low quality or indicates login/CAPTCHA:
   - `--wait-for interaction` for auto-detected gates (login, CAPTCHA, Cloudflare)
   - `--wait-for force` when the page needs manual browsing, scroll loading, or complex interaction
4. If `--wait-for` is used, tell the user exactly what to do:
   - Login required → sign in in the browser
   - CAPTCHA visible → solve it
   - Slow loading → wait until content is visible
   - `--wait-for force` → press Enter when ready
5. If JSON output shows `"status": "needs_interaction"`, switch to `--wait-for interaction` automatically

## Capture Modes

| Mode | Behavior | Use When |
|------|----------|----------|
| Default | Headless Chrome, auto-extract on network idle | Public pages, static content |
| `--headless` | Explicit headless (same as default) | Clarify intent |
| `--wait-for interaction` | Opens visible Chrome, auto-detects login/CAPTCHA gates, waits for them to clear, then continues | Login-required, CAPTCHA-protected |
| `--wait-for force` | Opens visible Chrome, auto-detects OR accepts Enter keypress to continue | Complex flows, lazy loading, paywalls |

**Interaction gate auto-detection**: Cloudflare Turnstile / "just a moment" pages, Google reCAPTCHA, hCaptcha, custom challenge / verification screens.
