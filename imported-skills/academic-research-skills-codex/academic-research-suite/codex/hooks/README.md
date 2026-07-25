# ARS Codex Hook Pack

The hook pack is disabled by default. It is only eligible for installation when
the user explicitly opts in with:

```bash
export ARS_CODEX_FULL_RUNTIME=1
export ARS_CODEX_HOOKS=1
```

`hooks.json` contains one read-only SessionStart announcement hook. It calls the
local Python wrapper in `codex/scripts/ars_codex_hook.py`, which prints adapter
metadata and command aliases only. It does not read environment variables, print
secrets, access the network, or write files.

Before installing or copying this hook pack into a Codex hook configuration, run:

```bash
python3 skills/academic-research-suite/codex/scripts/ars_codex_quality_gates.py hook-safety
```

Claude Code hooks in `ars/hooks/hooks.json` remain vendored upstream metadata.
They are not installed by this Codex adapter.
