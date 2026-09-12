import json
from pathlib import Path

base = Path(__file__).parent
json_path = base / "sections.json"
new_text_path = base / "statement_of_case_new.txt"

data = json.loads(json_path.read_text(encoding="utf-8"))
new_text = new_text_path.read_text(encoding="utf-8")

data["sections"]["statement_of_case"]["text"] = new_text
json_path.write_text(json.dumps(data, indent=4, ensure_ascii=False) + "\n", encoding="utf-8")
