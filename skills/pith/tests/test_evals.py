"""Pytest entry point for PITH eval suite (myskills standalone)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "scripts"))


def test_evals_pass():
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        "run_evals", Path(__file__).parent / "run_evals.py"
    )
    mod = importlib.util.module_from_spec(spec)  # type: ignore[arg-type]
    spec.loader.exec_module(mod)  # type: ignore[union-attr]
    result = mod.main()
    assert result == 0, f"Eval suite returned {result} (some evals failed — see output above)"
