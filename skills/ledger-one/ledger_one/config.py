from pathlib import Path
import yaml

UNCATEGORIZED = "Uncategorized"


def load_categories(path: Path) -> list[str]:
    data = yaml.safe_load(Path(path).read_text())
    cats = (data or {}).get("categories") or []
    if not cats:
        raise ValueError(f"No categories found in {path}")
    if UNCATEGORIZED not in cats:
        cats = list(cats) + [UNCATEGORIZED]
    return cats
