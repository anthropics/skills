---
name: xiao
description: >
  Control a Xiaomi Robot Vacuum X20+ (model xiaomi.vacuum.c102gl) through the `xiao`
  CLI. Use this skill whenever the user mentions anything vacuum-related: robot
  vacuum, Xiaomi, Roborock, cleaning the house, mopping, sweeping, dock, base
  station, consumables (brush, filter, mop pad), rooms, map, zones, DND mode, fan
  speed, vacuum status, battery, cleaning schedule. Also trigger on Spanish
  equivalents (aspiradora, limpiar, trapear, cargar, habitaciones, cepillo,
  filtro, base, programar limpieza) and casual phrasings (limpia la casa, pon la
  aspiradora, qué batería tiene, mándala al dock). When in doubt, trigger — the
  CLI handles all vacuum ops.
---

# xiao — Xiaomi Vacuum CLI Skill

The `xiao` CLI controls a Xiaomi Robot Vacuum X20+ via Xiaomi Cloud. Full
reference lives in [`AGENTS.md`](../../../AGENTS.md) at the repo root — **read
that first** for canonical commands, intent mapping, and error recovery.

## Prerequisites

Before any command will succeed:

1. `pip install xiao && playwright install chromium` (once per machine).
2. `xiao setup cloud` completed — produces `config.toml`.
3. Chromium on port `18800` with an active `account.xiaomi.com` session:
   ```bash
   chromium --remote-debugging-port=18800 --user-data-dir=~/.xiao-chromium
   ```

## Workflow for any user request

1. **Parse intent.** Check the "Intent mapping" table in `AGENTS.md`.
2. **Resolve room IDs** with `xiao map rooms` before any `xiao clean -r <id>`.
   Never guess. IDs are per-vacuum and regenerate when the Xiaomi Home app
   re-maps the house.
3. **Run the command.** Prefer `--json` for status-type commands so you can
   parse deterministically:
   ```bash
   xiao status --json
   xiao consumables --json
   ```
4. **On error**, apply the recovery protocol in `AGENTS.md#error-recovery`
   before asking the user:
   - Exit `77` or stderr contains `token`/`401` → retry once; if still bad,
     `xiao cloud-login` and retry.
   - Exit `2` or stderr says "Cloud mode enabled but not configured" → guide
     user through `xiao setup cloud`.
   - `Cannot connect to browser CDP on port 18800` → launch the Chromium
     instance described above and have the user log in once.
   - State 21 / "WashingMopPause" → user must refill clean water / empty
     dirty water, then `xiao start`.

## Exit codes (agent-meaningful)

| Code | Meaning | Action |
|---|---|---|
| `0` | Success | Continue |
| `2` | Not configured | Run `xiao setup cloud` |
| `77` | Cloud auth failed | Run `xiao cloud-login` |
| Other non-zero | Generic failure | Parse stderr / ask user |

## Hard rules

- **Never** print or commit the contents of `config.toml` — it holds the user's
  Xiaomi password hash and service tokens.
- **Never** call `xiao raw` unless the user explicitly asks. It's an unchecked
  escape hatch into MIoT that can brick settings.
- **Always** verify room IDs with `xiao map rooms` before using them in a
  `clean -r` call.
- `xiao start` always triggers a mop wash first. Warn the user if they asked
  for sweep-only; there's no flag to skip the wash.
