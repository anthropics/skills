# Browser Automation Canon — Screenshot-First + find()-Before-Click

This reference answers exactly one decision: **what discipline does the notebooklm skill follow when controlling NotebookLM's UI, and why?**

## The Core Frame

NotebookLM is a **dynamic single-page application** where the UI varies significantly by:

- Account tier (free / Plus / Enterprise)
- Feature rollout (Studio types not yet GA for all users)
- Time (Google iterates the product frequently — buttons move, labels change, layouts shift)
- A/B experiments (different users see different UIs)

Hard-coded coordinates break instantly when these change. Semantic discipline survives.

## The Two Disciplines

### 1. Screenshot-First

**Every meaningful UI action must be preceded by a screenshot.**

Reasons:

1. **Verify UI matches expectations** before acting (account-tier differences, A/B variants)
2. **Catch login walls early** before attempting actions on a not-logged-in page
3. **Detect unexpected layout changes** (Google ships UI changes weekly)
4. **Audit trail** for debugging when actions fail

The performance cost is negligible (screenshots are fast). The safety benefit is large.

### 2. find()-Before-Click

**Use semantic element finders before pixel coordinates.**

Pattern preference:

| Pattern | Survives | Use when |
|---|---|---|
| `find(text="Audio Overview")` | UI rearrangements | Element has stable visible text |
| `find(aria_label="Generate")` | A11y-labeled elements | Element has stable aria-label |
| `find(data_test="studio-btn")` | Internal test IDs | Element has stable data-* attribute (rare in NotebookLM) |
| `find(role="button", name="Send")` | Accessibility tree | Element role + accessible name stable |
| `click(x=420, y=380)` | Nothing | **Last resort only** — UI must visually align exactly |

### Why coordinates break

Google rolled out a UI redesign in Q2 2025 that moved the Studio panel from right-side to a collapsible drawer. Skills using pixel coordinates broke overnight. Skills using `find(text="Studio")` adapted automatically.

## The Tool-Agnostic Vocabulary

NotebookLM skill uses generic terms — NOT hardcoded to a specific tool:

| Skill says | Tool-specific implementation examples |
|---|---|
| "browser automation tool" | Claude computer-use, Claude Chrome Extension, Playwright, Puppeteer |
| "screenshot tool" | `screenshot()`, `page.screenshot()`, `browser.captureScreenshot()` |
| "find tool" | `find_element()`, `page.locator()`, `$$(selector)` |
| "click tool" | `click()`, `page.click()`, `element.click()` |
| "navigate tool" | `navigate()`, `page.goto()`, `browser.open()` |
| "file-upload tool" | Tool-specific file-upload mechanism (not native file picker) |

Why: the skill should work across browser-automation environments. Tool-specific code locks the skill to one harness.

## Critical Discipline: Never Click Native File Pickers

When uploading a file to NotebookLM:

❌ **Do NOT click the "Choose File" button** — this opens a native OS file picker that browser automation cannot control.

✅ **Use the file-upload tool** — your browser-automation environment provides a way to attach files programmatically. Example patterns:

- Playwright: `page.set_input_files(input_ref, file_path)`
- Computer-use: `upload_file(file_input_locator, absolute_path)`
- Puppeteer: `page.$eval(input_selector, (el, path) => el.files = ...)`

The file-upload tool bypasses the native picker entirely.

## Login Wall Discipline

NotebookLM requires Google authentication. Login walls can appear:

- Initial visit (not logged in)
- Session timeout (logged in but stale)
- Account switch (multiple Google accounts)
- 2FA challenge (security verification)

**Hard rule: never attempt to handle login automatically.**

Why:
- Credentials are sensitive
- 2FA requires human interaction
- Account state varies (logged in to wrong account, etc.)
- Browser-automation handling login creates security audit nightmares

Detection pattern:

```
1. Take screenshot
2. Check for login signals: "Sign in to Google", login URL, password field visible
3. If detected → halt with clear message: "Please log in to NotebookLM in your browser, then re-invoke this skill."
4. Do not type credentials, do not click login buttons
```

## Async Wait Discipline (See Also: async_action_discipline.md)

Different actions have different timing:

- **Fast (< 5s)**: chat send, basic clicks — wait synchronously
- **Medium (5-60s)**: source ingestion, auto-summary, Study Guide / Briefing Doc — wait with timeout
- **Slow (1-10 min)**: Audio Overview, Infographic, Slides — **fire-and-notify, don't wait**

Mis-applying the timing causes:
- Session timeout (user waits 10 min for Audio Overview to complete)
- False failure reports (skill thinks it failed because it timed out waiting)
- Wasted compute

## Screenshot Audit Pattern

For debugging + transparency, the skill should produce a screenshot trail per session:

```
~/notebooklm_sessions/<date>-<action>/
  001-step0-environment-check.png
  002-homepage-loaded.png
  003-notebook-found.png
  004-chat-input-located.png
  005-question-submitted.png
  006-response-received.png
```

Per-screenshot rationale:
- Step 0 baseline (proves environment was checked)
- Each UI interaction documented
- Final state captured

This is the audit-log equivalent for browser-automation skills.

## Anti-Patterns

### "Just click where it usually is"

Pixel coordinates. Breaks on any UI change. Most common failure mode.

### "Skip screenshots to save time"

The cost of skipping is unrecoverable: when something goes wrong, no audit trail exists. Always screenshot.

### "Try to handle login programmatically"

Security risk + brittle. Always halt and ask user to log in manually.

### "Wait for Audio Overview synchronously"

5-10 minute generations exceed session timeout. Fire-and-notify pattern.

### "Use the main Studio button"

Default Studio prompts produce mediocre output. Always open the customization menu (chevron next to main button) and write a custom prompt.

### "Hardcode 'Claude Chrome Extension'"

Tool-specific. Use "browser automation tool" or equivalent generic term.

### "Click 'Choose File' for uploads"

Opens native file picker, breaks automation. Use the file-upload tool.

## Operational Checklist (Per UI Action)

- [ ] Screenshot taken before action
- [ ] Semantic find() attempted before pixel coordinates
- [ ] Login wall check after navigation
- [ ] Tool-agnostic vocabulary in skill body
- [ ] File uploads use file-upload tool, not file picker
- [ ] Async timing classified correctly (wait vs fire-and-notify)
- [ ] Screenshot trail saved for audit

## Citations (7 sources)

1. **Anthropic Computer Use documentation (Claude 3.5 Sonnet + later).** Source for the screenshot-first + semantic-find discipline in Claude's official browser automation tool. The patterns in this reference are the production patterns Anthropic recommends.

2. **Playwright documentation — playwright.dev.** Source for the semantic locator patterns (`page.locator()`, role-based selectors, accessibility tree). Playwright's locator model is the modern standard.

3. **Selenium documentation + best practices guides.** Source for the historical context: Selenium pioneered semantic finders 15+ years before Playwright; the patterns are well-established.

4. **W3C Web Driver protocol.** Source for the standardized element-locator strategies (id, name, class, link text, partial link text, tag name, css, xpath). The protocol formalized what to find by.

5. **Microsoft Power Automate Desktop UI automation guidance.** Source for the "image-based selectors are last resort" guidance. Microsoft's enterprise RPA tooling formalized the same discipline.

6. **Google A11y / ARIA patterns — w3.org/WAI/ARIA/.** Source for the role + accessible-name selector strategy. ARIA labels are the most stable selector when present.

7. **Anthropic's "Tool Use" + browser automation cookbook (docs.anthropic.com).** Source for the tool-agnostic vocabulary discipline. Anthropic explicitly recommends generic "screenshot tool" / "click tool" language to keep skills portable across harnesses.
