#!/usr/bin/env python3
"""Build the standard split Chinese patent application package (materials-paper-to-patent)."""

import argparse
import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path


def run(command: list[str]) -> None:
    subprocess.run(command, check=True)


def validate(data: dict) -> None:
    required = ("title", "claims", "specification", "abstract", "figures")
    missing = [key for key in required if not data.get(key)]
    if missing:
        raise ValueError(f"Missing required complete-package content: {', '.join(missing)}")
    spec = data["specification"]
    if not spec.get("figure_descriptions"):
        raise ValueError("Specification must contain figure descriptions")
    if "equations" not in spec:
        raise ValueError(
            "Specification must contain an equations array; use an empty array only when "
            "the source contains no core technical formulas"
        )
    source_analysis = data.get("source_analysis", {})
    if source_analysis.get("contains_core_formulas") and not spec.get("equations"):
        raise ValueError(
            "The source is marked as containing core formulas, but specification.equations is empty"
        )
    for equation in spec.get("equations", []):
        if not equation.get("latex"):
            raise ValueError(
                f"Equation {equation.get('number')} must include latex source for native Office Math"
            )
    equation_numbers = [item.get("number") for item in spec.get("equations", [])]
    if equation_numbers and equation_numbers != list(range(1, len(equation_numbers) + 1)):
        raise ValueError(
            f"Equation numbers must be consecutive integers starting at 1: {equation_numbers}"
        )
    abstract_figure_number = data.get("abstract_figure_number")
    if not isinstance(abstract_figure_number, int):
        raise ValueError("abstract_figure_number must be an integer")
    figure = next(
        (
            item
            for item in data["figures"]
            if item.get("number") == abstract_figure_number
        ),
        None,
    )
    if figure is None:
        raise ValueError(
            f"abstract_figure_number {abstract_figure_number} does not reference an existing figure"
        )
    if not figure.get("complete_claim_flow"):
        raise ValueError("The abstract figure must be a complete principal claim flow")
    if source_analysis.get("contains_methodology_figures"):
        methodology = [item for item in data["figures"] if item.get("type") == "methodology"]
        if not methodology:
            raise ValueError(
                "The source is marked as containing methodology figures, but no methodology "
                "figure is included"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("draft", type=Path, help="UTF-8 patent draft JSON")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--prefix", default="patent")
    args = parser.parse_args()

    data = json.loads(args.draft.read_text(encoding="utf-8"))
    root = Path(__file__).resolve().parent
    validator_script = root / "validate_patent_draft.py"
    validator_spec = importlib.util.spec_from_file_location(
        "patent_draft_validator", validator_script
    )
    validator = importlib.util.module_from_spec(validator_spec)
    sys.modules[validator_spec.name] = validator
    validator_spec.loader.exec_module(validator)
    validation_findings = validator.validate_draft(data)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    validation_report = args.output_dir / f"{args.prefix}-草稿验证报告.txt"
    validation_report.write_text(
        validator.format_report(validation_findings), encoding="utf-8"
    )
    if any(item.severity == validator.Severity.ERROR for item in validation_findings):
        print(validation_report)
        raise SystemExit(1)

    validate(data)
    docx_script = root / "render_patent_docx.py"
    figure_script = root / "render_flowchart_svg.py"

    figure_dir = args.output_dir / f"{args.prefix}-figures"
    flow_steps = args.draft.parent / "flow-steps.json"
    if not flow_steps.exists():
        raise ValueError(f"Missing flowchart steps file: {flow_steps}")
    run(
        [
            sys.executable,
            str(figure_script),
            str(flow_steps),
            "--output",
            str(figure_dir / "figure-1.svg"),
            "--png-output",
            str(figure_dir / "figure-1.png"),
        ]
    )

    outputs = {
        "claims": args.output_dir / f"{args.prefix}-权利要求书.docx",
        "specification": args.output_dir / f"{args.prefix}-说明书.docx",
        "abstract": args.output_dir / f"{args.prefix}-说明书摘要.docx",
        "abstract-figure": args.output_dir / f"{args.prefix}-摘要附图.docx",
        "all": args.output_dir / f"{args.prefix}-完整审阅稿.docx",
    }
    for part, output in outputs.items():
        command = [
            sys.executable,
            str(docx_script),
            str(args.draft),
            "--output",
            str(output),
            "--part",
            part,
        ]
        if part in {"specification", "abstract", "abstract-figure", "all"}:
            command.extend(["--figure-dir", str(figure_dir)])
        run(command)

    claims_text = args.output_dir / f"{args.prefix}-权利要求书.txt"
    claims_text.write_text(
        "\n".join(f"{claim['number']}. {claim['text']}" for claim in data["claims"]) + "\n",
        encoding="utf-8",
    )
    audit = args.output_dir / f"{args.prefix}-权利要求检查.txt"
    audit_script = root / "audit_claims.py"
    spec = importlib.util.spec_from_file_location("patent_claim_audit", audit_script)
    audit_module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = audit_module
    spec.loader.exec_module(audit_module)
    findings = audit_module.audit(claims_text.read_text(encoding="utf-8"))
    if findings:
        lines = []
        for finding in findings:
            location = f"权利要求{finding.claim}" if finding.claim else "整体"
            lines.append(
                f"{finding.level}\t{location}\t{finding.code}\t{finding.message}"
            )
    else:
        lines = ["PASS: 未发现权利要求结构性问题。"]
    audit.write_text("\n".join(lines) + "\n", encoding="utf-8")
    if any(finding.level == "ERROR" for finding in findings):
        raise SystemExit(1)

    json_copy = args.output_dir / f"{args.prefix}-结构化草稿.json"
    if args.draft.resolve() != json_copy.resolve():
        shutil.copy2(args.draft, json_copy)

    for output in (*outputs.values(), json_copy, audit, validation_report):
        print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
