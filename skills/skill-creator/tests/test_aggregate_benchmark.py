import json
import shutil
import sys
import tempfile
from pathlib import Path
import pytest

# Add skill-creator scripts directory to path
SCRIPTS_DIR = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

import aggregate_benchmark as agg


@pytest.fixture
def temp_dir():
    d = tempfile.mkdtemp()
    yield Path(d)
    shutil.rmtree(d, ignore_errors=True)


def make_valid_grading(pass_rate=1.0, passed=2, failed=0, total=2):
    return {
        "expectations": [
            {
                "text": "Correct command was called",
                "passed": True,
                "evidence": "Executed az ad group member check",
            },
            {
                "text": "Output formatted as JSON",
                "passed": True,
                "evidence": "Output is valid JSON",
            },
        ],
        "summary": {
            "passed": passed,
            "failed": failed,
            "total": total,
            "pass_rate": pass_rate,
        },
        "timing": {
            "total_duration_seconds": 12.5,
        },
        "execution_metrics": {
            "total_tool_calls": 3,
            "errors_encountered": 0,
        },
    }


def test_workspace_layout(temp_dir):
    benchmark_dir = temp_dir / "benchmarks" / "iter-1"
    eval_dir = benchmark_dir / "eval-0"
    for config in ("with_skill", "without_skill"):
        run_dir = eval_dir / config / "run-1"
        run_dir.mkdir(parents=True, exist_ok=True)
        (run_dir / "grading.json").write_text(json.dumps(make_valid_grading()))

    results = agg.load_run_results(benchmark_dir)
    assert "with_skill" in results
    assert "without_skill" in results
    assert len(results["with_skill"]) == 1
    assert results["with_skill"][0]["eval_id"] == 0
    assert results["with_skill"][0]["run_number"] == 1


def test_legacy_layout(temp_dir):
    benchmark_dir = temp_dir / "legacy_benchmark"
    eval_dir = benchmark_dir / "runs" / "eval-1"
    for config in ("with_skill", "without_skill"):
        run_dir = eval_dir / config / "run-1"
        run_dir.mkdir(parents=True, exist_ok=True)
        (run_dir / "grading.json").write_text(json.dumps(make_valid_grading()))

    results = agg.load_run_results(benchmark_dir)
    assert "with_skill" in results
    assert len(results["with_skill"]) == 1
    assert results["with_skill"][0]["eval_id"] == 1


def test_descriptive_eval_names(temp_dir):
    benchmark_dir = temp_dir / "descriptive_benchmark"
    for eval_name in ("group-membership-check", "role-assignment-list"):
        eval_dir = benchmark_dir / eval_name
        eval_dir.mkdir(parents=True, exist_ok=True)
        (eval_dir / "config.json").write_text(json.dumps({"name": eval_name}))
        run_dir = eval_dir / "with_skill" / "run-1"
        run_dir.mkdir(parents=True, exist_ok=True)
        (run_dir / "grading.json").write_text(json.dumps(make_valid_grading()))

    results = agg.load_run_results(benchmark_dir)
    assert "with_skill" in results
    eval_ids = [r["eval_id"] for r in results["with_skill"]]
    assert "group-membership-check" in eval_ids
    assert "role-assignment-list" in eval_ids


def test_non_directory_files_ignored(temp_dir):
    benchmark_dir = temp_dir / "benchmark"
    eval_dir = benchmark_dir / "eval-0"
    config_dir = eval_dir / "with_skill"
    run_dir = config_dir / "run-1"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "grading.json").write_text(json.dumps(make_valid_grading()))

    # Add stray files in various places
    (benchmark_dir / ".DS_Store").write_text("junk")
    (benchmark_dir / "screenshot.png").write_text("binary")
    (eval_dir / "eval_notes.txt").write_text("notes")
    (config_dir / "run-log.txt").write_text("not a directory")

    results = agg.load_run_results(benchmark_dir)
    assert "with_skill" in results
    assert len(results["with_skill"]) == 1


def test_invalid_run_dir_name_ignored(temp_dir):
    benchmark_dir = temp_dir / "benchmark"
    config_dir = benchmark_dir / "eval-0" / "with_skill"
    # Valid run
    (config_dir / "run-1").mkdir(parents=True, exist_ok=True)
    ((config_dir / "run-1") / "grading.json").write_text(json.dumps(make_valid_grading()))
    # Invalid run directory names
    (config_dir / "run-backup").mkdir(parents=True, exist_ok=True)
    (config_dir / "run-").mkdir(parents=True, exist_ok=True)
    (config_dir / "invalid-1").mkdir(parents=True, exist_ok=True)

    results = agg.load_run_results(benchmark_dir)
    assert len(results["with_skill"]) == 1
    assert results["with_skill"][0]["run_number"] == 1


def test_missing_grading_file(temp_dir, capsys):
    benchmark_dir = temp_dir / "benchmark"
    run_dir = benchmark_dir / "eval-0" / "with_skill" / "run-1"
    run_dir.mkdir(parents=True, exist_ok=True)
    # No grading.json created

    results = agg.load_run_results(benchmark_dir)
    assert results.get("with_skill") == []
    captured = capsys.readouterr()
    assert "Warning: grading.json not found" in captured.out


def test_malformed_json_grading(temp_dir, capsys):
    benchmark_dir = temp_dir / "benchmark"
    run_dir = benchmark_dir / "eval-0" / "with_skill" / "run-1"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "grading.json").write_text("{this is not valid json")

    results = agg.load_run_results(benchmark_dir)
    assert results.get("with_skill") == []
    captured = capsys.readouterr()
    assert "Warning: Invalid JSON" in captured.out


def test_expectation_schema_validation_and_normalization(temp_dir, capsys):
    benchmark_dir = temp_dir / "benchmark"
    run_dir = benchmark_dir / "eval-0" / "with_skill" / "run-1"
    run_dir.mkdir(parents=True, exist_ok=True)

    grading = {
        "expectations": [
            # Standard valid schema
            {"text": "Criteria 1", "passed": True, "evidence": "Found in step 1"},
            # Missing evidence (should warn and default)
            {"text": "Criteria 2", "passed": False},
            # Variant field names: name/met/details (should warn and normalize)
            {"name": "Criteria 3", "met": True, "details": "Found in step 3"},
            # Invalid non-dict (should warn and skip)
            "invalid string expectation",
        ],
        "summary": {"passed": 2, "failed": 1, "total": 3, "pass_rate": 0.67},
    }
    (run_dir / "grading.json").write_text(json.dumps(grading))

    results = agg.load_run_results(benchmark_dir)
    assert "with_skill" in results
    exps = results["with_skill"][0]["expectations"]
    assert len(exps) == 3
    assert exps[0] == {"text": "Criteria 1", "passed": True, "evidence": "Found in step 1"}
    assert exps[1] == {"text": "Criteria 2", "passed": False, "evidence": ""}
    assert exps[2]["text"] == "Criteria 3"
    assert exps[2]["passed"] is True
    assert exps[2]["evidence"] == "Found in step 3"

    captured = capsys.readouterr()
    assert "missing required fields" in captured.out
    assert "not a dict" in captured.out


def test_mixed_eval_ids_generate_benchmark(temp_dir):
    benchmark_dir = temp_dir / "benchmark"
    # Integer eval_id
    run_dir1 = benchmark_dir / "eval-1" / "with_skill" / "run-1"
    run_dir1.mkdir(parents=True, exist_ok=True)
    (run_dir1 / "grading.json").write_text(json.dumps(make_valid_grading()))

    # String eval_id
    run_dir2 = benchmark_dir / "auth-test" / "with_skill" / "run-1"
    run_dir2.mkdir(parents=True, exist_ok=True)
    (run_dir2 / "grading.json").write_text(json.dumps(make_valid_grading()))

    bench = agg.generate_benchmark(benchmark_dir, "test-skill")
    assert bench["metadata"]["evals_run"] == [1, "auth-test"]
    assert "with_skill" in bench["run_summary"]
