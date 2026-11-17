READ [SKILL-CREATOR] FOR INSTRUCTIONS [D:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\skills\skill-creator]

RUN ORDER FOR ANY MODEL ENTERING SKILLS:
1) BEFORE DOING ANY WORK: run `python scripts/build_index.py` from skills/. This generates skills_index.json, skills_index.md, and appends MASTER_LOG.md. Review the issues list before touching files.
2) DO WORK following the per-skill instruction packs.
3) AFTER WORK: run `python scripts/build_index.py` again to capture the final state and surface any broken/missing files. If the script reports issues, fix them or leave a note in the relevant instruction pack.

STRUCTURE THAT MUST NEVER CHANGE (PER SKILL ROOT):
1. SKILL.md (must be named SKILL.md)
2. LICENSE or LICENSE.txt
3. [tool_name]_instructions/ (folder named exactly after the tool dir plus `_instructions`) with numbered files in read order.
4. Older skills may also have "scripts" or "references" dirs. Those stay, but do not add other root clutter.

Naming: [tool_name] must match the parent folder exactly (skills/[tool_name]/).

The instructions folder must contain numbered files in the order to be read. If a file is optional, it still stays in order so the model can decide at run time.

This dir is simple to see the setup because it keeps getting messy... and it can't get messy anymore.


