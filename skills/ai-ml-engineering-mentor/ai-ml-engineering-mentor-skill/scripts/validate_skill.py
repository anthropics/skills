from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
skill = ROOT / "SKILL.md"

errors = []

if not skill.exists():
    errors.append("SKILL.md is missing")
else:
    text = skill.read_text(encoding="utf-8")
    if not text.startswith("---\n"):
        errors.append("SKILL.md must start with YAML frontmatter")
    else:
        parts = text.split("---", 2)
        if len(parts) < 3:
            errors.append("Malformed YAML frontmatter")
        else:
            front = parts[1]
            name = re.search(r"^name:\s*(.+)$", front, re.M)
            desc = re.search(r"^description:\s*(.+)$", front, re.M)
            if not name:
                errors.append("Missing name")
            else:
                value = name.group(1).strip()
                if not re.fullmatch(r"[a-z0-9-]{1,64}", value):
                    errors.append("name must be lowercase letters, numbers, and hyphens")
            if not desc:
                errors.append("Missing description")
            elif len(desc.group(1).strip()) > 1024:
                errors.append("description exceeds 1024 characters")

required = [
    "references/learning-framework.md",
    "references/debugging-playbook.md",
    "references/ml-workflow.md",
    "references/rag-and-agents.md",
    "references/project-workflow.md",
    "evaluations/test-cases.md",
]

for item in required:
    if not (ROOT / item).exists():
        errors.append(f"Missing required file: {item}")

if errors:
    print("INVALID")
    for error in errors:
        print("-", error)
    raise SystemExit(1)

print("VALID")
print("Skill structure and frontmatter checks passed.")
