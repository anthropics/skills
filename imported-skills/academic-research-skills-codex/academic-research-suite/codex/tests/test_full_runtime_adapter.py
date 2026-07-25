from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path


CODEX_ROOT = Path(__file__).resolve().parents[1]
SUITE_ROOT = CODEX_ROOT.parent
PLANNER_PATH = CODEX_ROOT / "scripts" / "ars_codex_full_runtime.py"
GATES_PATH = CODEX_ROOT / "scripts" / "ars_codex_quality_gates.py"
MODEL_TIERING_CHECK = SUITE_ROOT / "ars" / "scripts" / "check_model_tiering.py"


def _load_planner():
    spec = importlib.util.spec_from_file_location("ars_codex_full_runtime", PLANNER_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


def test_vague_paper_topic_routes_to_deep_research_socratic() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "Use $academic-research-suite. I want to write a paper on AI adoption in higher education quality assurance. I do not yet have a clear research question.",
        env={},
    )
    assert plan["workflow"] == "deep-research"
    assert plan["mode"] == "socratic"
    assert plan["route_reason"] == "paper_topic_scoping_override"


def test_vague_topic_with_unclear_research_question_still_routes_to_socratic() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "Use $academic-research-suite. I want to write a paper on AI governance in universities, but my research question is still unclear.",
        env={},
    )
    assert plan["workflow"] == "deep-research"
    assert plan["mode"] == "socratic"
    assert plan["route_reason"] == "paper_topic_scoping_override"


def test_ars_plan_routes_to_academic_paper_plan_when_rq_exists() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "ars-plan Research question: How do QA agencies evaluate AI governance in universities?",
        env={},
    )
    assert plan["command_alias"] == "ars-plan"
    assert plan["workflow"] == "academic-paper"
    assert plan["mode"] == "plan"
    assert plan["command_recipe"] == "ars/commands/ars-plan.md"


def test_ars_lit_review_alias_routes_to_lit_review_mode() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "ars-lit-review Research question: What is known about AI governance in university QA?",
        env={},
    )
    assert plan["workflow"] == "academic-paper"
    assert plan["mode"] == "lit-review"


def test_ars_cache_invalidate_alias_routes_to_pipeline_cache_mode() -> None:
    planner = _load_planner()
    plan = planner.plan_request("ars-cache-invalidate smith2024", env={})
    assert plan["command_alias"] == "ars-cache-invalidate"
    assert plan["workflow"] == "academic-pipeline"
    assert plan["mode"] == "cache-invalidate"
    assert plan["command_recipe"] == "ars/commands/ars-cache-invalidate.md"


def test_ars_3w_alias_routes_to_deep_research_three_way_scan() -> None:
    planner = _load_planner()
    plan = planner.plan_request("ars-3w compare these three papers", env={})
    assert plan["command_alias"] == "ars-3w"
    assert plan["workflow"] == "deep-research"
    assert plan["mode"] == "three-way-scan"
    assert plan["command_recipe"] == "ars/commands/ars-3w.md"


def test_ars_rebuttal_audit_alias_routes_to_academic_paper() -> None:
    planner = _load_planner()
    plan = planner.plan_request("ars-rebuttal-audit check my response draft against these reviewer comments", env={})
    assert plan["command_alias"] == "ars-rebuttal-audit"
    assert plan["workflow"] == "academic-paper"
    assert plan["mode"] == "rebuttal-audit"
    assert plan["command_recipe"] == "ars/commands/ars-rebuttal-audit.md"


def test_korean_revision_routes_to_academic_paper_not_reviewer() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "이 논문을 수정해줘. 심사 의견은 아직 없고, 초고를 더 다듬고 싶어.",
        env={},
    )
    assert plan["workflow"] == "academic-paper"
    assert plan["mode"] == "revision"


def test_korean_review_routes_to_reviewer_not_revision() -> None:
    planner = _load_planner()
    plan = planner.plan_request("이 논문을 심사해줘.", env={})
    assert plan["workflow"] == "academic-paper-reviewer"
    assert plan["mode"] == "full"


def test_model_tiering_is_surfaced_without_forcing_a_codex_model() -> None:
    planner = _load_planner()
    inline = planner.plan_request("ars-plan Research question: Why?", env={"ARS_MODEL_TIERING": "economy"})
    assert inline["profile"]["model_tiering_status"] == "inline_noop"

    delegated = planner.plan_request(
        "ars-plan Research question: Why?",
        env={
            "ARS_CODEX_FULL_RUNTIME": "1",
            "ARS_CODEX_AGENT_TEAM": "1",
            "ARS_MODEL_TIERING": "quality-boost",
        },
    )
    assert delegated["profile"]["model_tiering_status"] == "advisory_requires_runtime_model_override"
    assert delegated["profile"]["model_tiering_requested"] == "quality-boost"


def test_ars_full_starts_pipeline_and_stops_at_dashboard_checkpoint() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "ars-full Research question: How do QA agencies evaluate AI governance? Stop after producing the pipeline dashboard.",
        env={"ARS_CODEX_FULL_RUNTIME": "1", "ARS_CODEX_AGENT_TEAM": "1"},
    )
    assert plan["profile"]["execution_mode"] == "codex_agent_team"
    assert plan["workflow"] == "academic-pipeline"
    assert plan["mode"] == "pipeline"
    assert plan["stop_at_checkpoint"] == "pipeline_dashboard"
    assert [item["agent"] for item in plan["agent_team_plan"]][:2] == [
        "pipeline_orchestrator_agent",
        "state_tracker_agent",
    ]


def test_reviewer_full_agent_team_keeps_synthesis_after_independent_reviews() -> None:
    planner = _load_planner()
    plan = planner.plan_request(
        "ars-reviewer full review for this manuscript.",
        env={"ARS_CODEX_FULL_RUNTIME": "1", "ARS_CODEX_AGENT_TEAM": "1"},
    )
    agents = [item["agent"] for item in plan["agent_team_plan"]]
    assert plan["workflow"] == "academic-paper-reviewer"
    assert plan["mode"] == "full"
    assert "editorial_synthesizer_agent" == agents[-1]
    assert "methodology_reviewer_agent" in agents[:-1]
    assert "devils_advocate_reviewer_agent" in agents[:-1]
    for item in plan["agent_team_plan"][:-1]:
        assert item["dispatch"] == "parallel_independent_review"
    assert plan["agent_team_plan"][-1]["dispatch"] == "after_independent_reviews"


def test_cli_outputs_json_plan() -> None:
    result = subprocess.run(
        [sys.executable, str(PLANNER_PATH), "ars-reviewer", "full", "review"],
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(result.stdout)
    assert payload["workflow"] == "academic-paper-reviewer"
    assert payload["mode"] == "full"


def test_quality_gates_all_pass() -> None:
    result = subprocess.run(
        [sys.executable, str(GATES_PATH), "all", "--json"],
        cwd=SUITE_ROOT.parents[1],
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(result.stdout)
    assert all(item["ok"] for item in payload.values()), payload


def test_model_tiering_lint_accepts_separately_vendored_experiment_agents() -> None:
    result = subprocess.run(
        [sys.executable, str(MODEL_TIERING_CHECK)],
        cwd=SUITE_ROOT / "ars",
        check=True,
        capture_output=True,
        text=True,
    )
    assert "39 agents classified" in result.stdout
