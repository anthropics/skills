# PreToolUse Hook Discipline — When To Block, When To Warn

This reference answers one decision: **when designing a PreToolUse hook for Claude Code, when should it block the tool call (exit 2) vs. just warn (exit 0 with stderr message)?** The answer depends on **reversibility × severity × false-positive rate**.

## The Three Exit Codes

Claude Code PreToolUse hooks have three meaningful exit codes:

| Exit code | Effect | Use when |
|---|---|---|
| `0` | Allow the tool call to proceed | No issue detected, or warning-only emission |
| `1` | Allow but log error | Hook itself errored — don't block the user |
| `2` | Block the tool call | Detected pattern is severe enough to require Claude to revisit |

## The Decision Matrix

```
                  High severity     Low severity
                  ─────────────     ───────────────
Hard to reverse   BLOCK (exit 2)    WARN (stderr + exit 0)
Easy to reverse   WARN              ALLOW (exit 0, no message)
```

Examples:

- **`eval(<user_input>)`** in production code: high severity (RCE), hard to reverse if it ships → **BLOCK**
- **`document.write` in a test file**: medium severity, easy to reverse → **WARN** (so the user can override deliberately)
- **`pickle.load` in a one-off script for the user's own data**: low severity in context, easy to reverse → **WARN**
- **Editing `.env` file**: high severity (secrets), but the user explicitly asked → **WARN** (let the user proceed)

## Session-State Caching

The security-guidance hook caches "warning shown" state per session. This is critical UX:

**Without caching:** Every Edit/Write to the same file triggers the same warning. Claude burns through tokens re-explaining + the user trains themselves to ignore. **Anti-pattern.**

**With caching:** First trigger blocks → Claude/user acknowledges → subsequent edits to same file+rule allowed for rest of session. **Correct.**

The caching is keyed by `<file_path>-<rule_name>`. Different rules on the same file each trigger independently (a file might warn for both `eval(` and `os.system` — and should).

## False-Positive Tolerance

A PreToolUse hook with a 50% false-positive rate is a hook nobody listens to. The pattern table needs to be calibrated for **high precision, accepting some recall loss**.

Calibration questions per pattern:

1. **Specificity:** Does the pattern uniquely identify the anti-pattern, or does it match many safe uses?
2. **Context-blindness:** Does the substring trigger inside string literals or comments? (Acceptable cost for cross-language detection.)
3. **Override path:** Can the user document a legitimate use case? (E.g., comment annotation.)

For the security-guidance hook's 12 patterns, false-positive rates are roughly:

| Pattern | FP rate (estimated) | Why |
|---|---|---|
| `eval(` | ~5% | Mostly only appears in code-eval contexts; very low FP |
| `pickle` | ~30% | Includes `import pickle` and any reference to the module |
| `innerHTML =` | ~10% | Pretty specific to the anti-pattern |
| GitHub Actions path-check | ~0% | Path-based, never false-positive |
| SQL f-string | ~15% | Could match harmless f-strings |

Higher-FP patterns rely on session-caching: user dismisses once, no nag for rest of session.

## When Substring Detection Is Enough

For Claude Code PreToolUse hooks, substring detection is sufficient when:

- The substring is rare in non-anti-pattern contexts (e.g., `dangerouslySetInnerHTML`)
- The user can quickly dismiss a false positive (one-key acknowledgment)
- The cost of a false negative is high (security regression)

When substring detection is **NOT** enough:

- Patterns with high natural occurrence (e.g., the word "password" — appears in legitimate docs)
- Patterns where context matters semantically (a function called `safe_eval` should not match `eval(`)
- Patterns that require taint analysis (knowing if data came from user input)

For taint-aware analysis, layer in proper SAST in CI — don't push that complexity into the PreToolUse hook.

## Hook Performance Discipline

The hook runs **before every Edit/Write/MultiEdit**. Performance matters:

- Substring scan of 12 patterns: ~1ms for typical file content
- State file load/save: ~5ms (JSON, single file)
- Total overhead: ~10ms per tool call

This is well within tolerance. If a hook adds >100ms per tool call, it slows down Claude Code interactively.

**Don't:** Spawn child processes from the hook (kills latency).
**Don't:** Make network calls from the hook (kills latency + introduces failure modes).
**Do:** Keep all logic in-process; only use stdlib.

## Disable-Via-Env-Var Discipline

`ENABLE_SECURITY_REMINDER=0` disables the hook for a session. Use sparingly. The pattern:

- **Default ON** (this is the safe default)
- **Disable when:** doing a verified-safe operation that would otherwise trip a pattern (e.g., writing a deliberately-unsafe sandboxed REPL, doing security research)
- **Re-enable immediately** after the operation

Don't put `export ENABLE_SECURITY_REMINDER=0` in your shell rc file. That's the anti-pattern of training-yourself-to-ignore-warnings.

## Anti-Patterns

### Hook that always exits 0

If a hook never blocks and never warns, it has no effect. Remove it.

### Hook that always exits 2 on a pattern hit

If a hook always blocks, even on the 5th occurrence of a pattern the user already saw 4 times, the user disables the hook. Session-state caching is required.

### Hook with network I/O

Defeats latency budget + adds failure modes (what if the API is down?). Hooks should be hermetic.

### Hook that modifies state Claude can't see

If the hook silently mutates files or env vars, Claude doesn't know about the changes and may produce inconsistent next actions. Hooks should be observation-only or emit explicit warnings.

### Hook with regex that's hard to read

The pattern table should be reviewable by a non-author. If the regex is dense Perl-style, port to plain substring or simplify the regex. Maintainability >> cleverness for security code.

## Citations (7 sources)

1. **Anthropic — Claude Code hooks documentation (2024-2026).** Source for the canonical PreToolUse exit code semantics, hook input/output format, and ~10ms latency budget. https://docs.claude.com/en/docs/claude-code/hooks

2. **OWASP — Top 10 Web Application Security Risks (2021, current ed.).** Source for which patterns to detect: injection (A03), insecure design (A04), security misconfiguration (A05), broken authentication (A07). The hook's pattern table maps directly to these categories.

3. **CWE (Common Weakness Enumeration) — Top 25 Most Dangerous Software Weaknesses (current ed.).** Source for the specific weakness classes the hook catches: CWE-78 (OS command injection), CWE-79 (XSS), CWE-89 (SQL injection), CWE-94 (code injection), CWE-502 (deserialization). https://cwe.mitre.org/top25/

4. **GitHub Security Lab — "How to catch GitHub Actions workflow injections before attackers do" (2023).** Source for the GitHub Actions workflow path-based pattern. The cited blog post is referenced in the hook's warning text. https://github.blog/security/vulnerability-research/how-to-catch-github-actions-workflow-injections-before-attackers-do/

5. **Python.org — `pickle` module documentation (security warnings).** Source for the warning text on pickle deserialization RCE risk. https://docs.python.org/3/library/pickle.html

6. **PyYAML — Documentation on yaml.load vs yaml.safe_load (security warnings).** Source for the yaml.unsafe_load pattern. https://pyyaml.org/wiki/PyYAMLDocumentation

7. **React documentation — `dangerouslySetInnerHTML` security warnings.** Source for the React XSS pattern. https://react.dev/reference/react-dom/components/common#dangerously-setting-the-inner-html

8. **NIST — Secure Software Development Framework (SSDF, current ed.).** Source for the "shift-left" principle that motivates PreToolUse hooks: detect security issues at the earliest possible point in the development lifecycle, before they hit version control.
