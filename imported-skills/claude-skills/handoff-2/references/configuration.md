# Configuration Reference

The handoff skill is configurable. This document is the field-by-field reference. Setup walks the user through the questions interactively on first run; this doc is for re-reading the config later.

## Config file locations

| Scope | Path | Precedence |
|---|---|---|
| Project | `<repo>/.handoff/config.json` | Highest. Overrides global. |
| Global | `~/.config/handoff/config.json` | Default for the user. |
| Built-in defaults | (none — hardcoded in `config_loader.py`) | Lowest. |

Effective config = defaults ← global override ← project override.

## First-run prompt behaviour

On first invocation of `/cs:handoff`, the skill detects whether a config exists. If none does, it asks:

> Run setup now? (Y/n)

- **Y** — walks the 5 core questions (and 2 optional) and writes the global config. Then continues with the original handoff request.
- **N** — uses built-in defaults for this run (OS temp dir, 7-day retention, strict redaction, git context on, scan all skills). Writes a sentinel at `~/.config/handoff/.setup-declined` so the prompt never re-appears.

Rerun setup any time with `/cs:handoff-setup` (re-prompts and writes config; removes the decline sentinel automatically).

## Field reference

### `save_location.mode` — where handoffs go

| Value | Effect |
|---|---|
| `temp` | `mktemp -t handoff-XXXXXX.md`. Ephemeral. Zero project clutter. Matches Matt's original. |
| `home_visible` | `~/handoffs/<filename>`. Visible personal archive. |
| `home_hidden` | `~/.handoff/<filename>`. Hidden personal archive. |
| `project` | `<repo>/.handoff/<filename>`. Per-project, auto-gitignored on setup. |
| `custom` | Uses `save_location.path` verbatim. Power users / shared drives. |

**No default.** First-run setup asks the user explicitly.

### `save_location.path` — resolved directory

Set automatically by setup once `mode` is chosen. For `custom`, the user supplies it; the script validates writability before saving.

### `retention_days` — auto-cleanup window

| Value | Effect |
|---|---|
| `7` (recommended for temp) | Cleanup script deletes scaffolds older than 7 days. |
| `30` | Quarterly cleanup. |
| `0` | Forever. Cleanup never deletes. |
| `-1` | Manual. Cleanup is a no-op. |

Cleanup runs at the start of each `/cs:handoff` invocation. It is **mtime-guarded**: files with `mtime > ctime + 2s` (i.e., edited by the user after creation) are never deleted.

### `redaction` — linter strictness

| Value | Behaviour |
|---|---|
| `strict` (recommended) | Linter exits 1 on findings. Save is blocked until findings are resolved or whitelisted. |
| `warn` | Linter exits 0. Findings are printed; save proceeds. |
| `off` | Linter is not run. Not recommended. |

The inline whitelist marker is `<!-- handoff:allow secret -->`. See [redaction_checklist.md](redaction_checklist.md).

### `include_git_context` — auto git block

| Value | Effect |
|---|---|
| `true` (recommended) | Template generator runs `git branch --show-current`, `git log -1 --oneline`, `git status --porcelain` and pastes a short block at the top of State of play. |
| `false` | No git block. |

Silently skipped when not in a git repo.

### `skill_recommendation_scope` — recommender breadth

| Value | Effect |
|---|---|
| `all` (recommended) | Recommender scans every SKILL.md in the repo. |
| `current_domain` | Scans only the current domain folder (e.g. `productivity/`). |
| `off` | Recommender returns no suggestions; agent picks skills manually. |

Hard cap at 5 results, regardless of scope.

### `filename_style` — saved file naming

Applies when `save_location.mode != temp`.

| Value | Example |
|---|---|
| `date_slug` (recommended) | `2026-05-21-finish-redaction-linter.md` |
| `timestamp` | `handoff-20260521-174200.md` |
| `mktemp` | `handoff-XXXXXX.md` (random suffix) |

For `temp` mode, `filename_style` is always `mktemp`.

### `setup_completed_at` — ISO timestamp

Set automatically by setup. Read by `config_loader.setup_completed()` to decide whether to show the first-run prompt.

## Per-project overrides

To set project-specific overrides:

```bash
python3 productivity/handoff/skills/handoff/scripts/setup.py --reconfigure --project
```

Writes `<repo>/.handoff/config.json`. Missing keys fall back to the global config.

When `save_location.mode = project`, setup also offers to append `.handoff/` to `.gitignore`. Recommended — handoffs are working documents and rarely belong in version control.

## SessionStart hook

The SessionStart hook (`hooks/session_start.py`) is wired via `hooks/hooks.json`. It reads the same config as the rest of the skill. Disable per-session with:

```bash
HANDOFF_SESSIONSTART=0
```

The hook surfaces the most recent handoff (within the retention window) wrapped in `<handoff_from_previous_session>` tags. The agent reads it as data, not instructions.

## Sources

- XDG Base Directory Specification — `~/.config/<app>/` for user configs.
- Twelve-Factor App, Config (factor III) — config in the environment / standard locations.
- Anthropic, *Claude Code plugin configuration* — `${CLAUDE_PLUGIN_ROOT}` and hook wiring.
- POSIX `mktemp(1)` — atomic temp-file creation semantics.
- Atlassian Confluence, *page lifecycle and retention* — the precedent for mtime-guarded cleanup.
- Honeycomb, *Observability config patterns* — defaults that are safe; opt-ins that are explicit.
