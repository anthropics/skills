"""LLM backend abstraction for skill-creator scripts.

Provides a unified interface for making LLM calls across multiple backends:
1. GitHub Models API (gh auth token) -- OpenAI-compatible, no extra setup
2. claude CLI -- original Claude Code approach
3. Anthropic API (ANTHROPIC_API_KEY) -- direct API access

Backend selection order:
- If `claude` CLI is in PATH, use it (original behavior)
- If ANTHROPIC_API_KEY is set, use Anthropic API
- If `gh auth token` succeeds, use GitHub Models API
- Otherwise, raise an error

For trigger evaluation (tool-use detection), the API backends construct a
system prompt with available_skills and a mock `use_skill` tool, then check
whether the model calls the tool for the target skill.

For text completion (description improvement), the API backends send the
prompt as a user message and return the text response.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from typing import Any


def _get_gh_token() -> str | None:
    """Get GitHub auth token via `gh auth token`."""
    if not shutil.which("gh"):
        return None
    try:
        result = subprocess.run(
            ["gh", "auth", "token"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
    except Exception:
        pass
    return None


def _has_claude_cli() -> bool:
    """Check if the claude CLI binary is available."""
    return shutil.which("claude") is not None


def _has_anthropic_key() -> bool:
    """Check if ANTHROPIC_API_KEY is set."""
    return bool(os.environ.get("ANTHROPIC_API_KEY"))


def detect_backend() -> str:
    """Detect the best available backend.

    Returns one of: 'claude_cli', 'anthropic_api', 'github_models'
    Raises RuntimeError if no backend is available.
    """
    if _has_claude_cli():
        return "claude_cli"
    if _has_anthropic_key():
        return "anthropic_api"
    if _get_gh_token():
        return "github_models"
    raise RuntimeError(
        "No LLM backend available. Install the claude CLI, set ANTHROPIC_API_KEY, "
        "or authenticate with `gh auth login`."
    )


def _urlopen_with_retry(
    req: urllib.request.Request,
    timeout: int,
    max_retries: int = 5,
    base_delay: float = 2.0,
) -> Any:
    """Make an HTTP request with exponential backoff on 429/5xx errors."""
    last_error = None
    for attempt in range(max_retries):
        try:
            return urllib.request.urlopen(req, timeout=timeout)
        except urllib.error.HTTPError as e:
            if e.code == 429 or e.code >= 500:
                last_error = e
                delay = base_delay * (2 ** attempt) + random.uniform(0, 1)
                print(f"  Retry {attempt + 1}/{max_retries} after HTTP {e.code}, waiting {delay:.1f}s", file=sys.stderr)
                time.sleep(delay)
                # Re-create the request since the data stream may be consumed
                req = urllib.request.Request(
                    req.full_url,
                    data=req.data,
                    headers=dict(req.headers),
                    method=req.get_method(),
                )
                continue
            raise
        except Exception:
            raise
    raise last_error or RuntimeError("All retries exhausted")


def _resolve_model(model: str | None, backend: str) -> str:
    """Map a model name to the appropriate backend-specific identifier."""
    if backend == "github_models":
        # GitHub Models uses OpenAI model names
        # Map common Claude/generic model names to available models
        if model is None:
            return "gpt-4o"
        lower = model.lower()
        if "claude" in lower or "sonnet" in lower or "opus" in lower or "haiku" in lower:
            # Claude isn't available on GitHub Models free tier; use gpt-4o
            return "gpt-4o"
        return model
    # For claude_cli and anthropic_api, pass through
    return model or "claude-sonnet-4-20250514"


# ---------------------------------------------------------------------------
# Text completion (for improve_description.py)
# ---------------------------------------------------------------------------


def complete_text(prompt: str, model: str | None = None, backend: str | None = None, timeout: int = 300) -> str:
    """Send a prompt and return the text response.

    Used by improve_description.py to generate improved skill descriptions.
    """
    if backend is None:
        backend = detect_backend()
    model = _resolve_model(model, backend)

    if backend == "claude_cli":
        return _complete_text_claude_cli(prompt, model, timeout)
    elif backend == "anthropic_api":
        return _complete_text_anthropic_api(prompt, model, timeout)
    elif backend == "github_models":
        return _complete_text_github_models(prompt, model, timeout)
    else:
        raise ValueError(f"Unknown backend: {backend}")


def _complete_text_claude_cli(prompt: str, model: str | None, timeout: int) -> str:
    """Original claude CLI approach."""
    cmd = ["claude", "-p", "--output-format", "text"]
    if model:
        cmd.extend(["--model", model])

    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}

    result = subprocess.run(
        cmd,
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
        timeout=timeout,
    )
    if result.returncode != 0:
        raise RuntimeError(f"claude -p exited {result.returncode}\nstderr: {result.stderr}")
    return result.stdout


def _complete_text_anthropic_api(prompt: str, model: str, timeout: int) -> str:
    """Direct Anthropic Messages API call."""
    api_key = os.environ["ANTHROPIC_API_KEY"]
    body = json.dumps({
        "model": model,
        "max_tokens": 4096,
        "messages": [{"role": "user", "content": prompt}],
    })

    req = urllib.request.Request(
        "https://api.anthropic.com/v1/messages",
        data=body.encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        },
    )

    with _urlopen_with_retry(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))

    # Extract text from response
    text_parts = []
    for block in data.get("content", []):
        if block.get("type") == "text":
            text_parts.append(block["text"])
    return "\n".join(text_parts)


def _complete_text_github_models(prompt: str, model: str, timeout: int) -> str:
    """GitHub Models API (OpenAI-compatible)."""
    token = _get_gh_token()
    if not token:
        raise RuntimeError("Failed to get gh auth token")

    body = json.dumps({
        "model": model,
        "max_tokens": 4096,
        "messages": [{"role": "user", "content": prompt}],
    })

    req = urllib.request.Request(
        "https://models.inference.ai.azure.com/chat/completions",
        data=body.encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        },
    )

    with _urlopen_with_retry(req, timeout=timeout) as resp:
        data = json.loads(resp.read().decode("utf-8"))

    return data["choices"][0]["message"]["content"]


# ---------------------------------------------------------------------------
# Trigger evaluation (for run_eval.py)
# ---------------------------------------------------------------------------


TRIGGER_SYSTEM_PROMPT = """You are a helpful AI assistant with access to specialized skills.

When a user sends you a task, you should decide whether to use one of your available skills.
Skills provide specialized instructions for specific domains. You should use a skill
when the user's task clearly matches its description.

Available skills:
{skills_list}

If a task matches a skill's description, call the `use_skill` tool with the skill name.
If the task does not match any skill, respond with a short text message explaining
you would handle the task directly without any skill. Do NOT call the tool if
the task is not a good match."""


USE_SKILL_TOOL_OPENAI = {
    "type": "function",
    "function": {
        "name": "use_skill",
        "description": "Invoke a skill to handle the user's task",
        "parameters": {
            "type": "object",
            "properties": {
                "skill": {
                    "type": "string",
                    "description": "The name of the skill to invoke",
                },
            },
            "required": ["skill"],
        },
    },
}

USE_SKILL_TOOL_ANTHROPIC = {
    "name": "use_skill",
    "description": "Invoke a skill to handle the user's task",
    "input_schema": {
        "type": "object",
        "properties": {
            "skill": {
                "type": "string",
                "description": "The name of the skill to invoke",
            },
        },
        "required": ["skill"],
    },
}


def _build_skills_list(skill_name: str, skill_description: str, other_skills: list[dict] | None = None) -> str:
    """Build the available_skills list for the system prompt.

    Includes the target skill plus some realistic decoy skills to make the
    evaluation more realistic (the model should pick the right one).
    """
    skills = []

    # Default decoy skills that are realistic neighbors
    default_decoys = [
        {"name": "github-prs", "description": "Manage GitHub pull requests via GitHub CLI. Create PRs, inspect changes, list files and hunks, read comments, reply to comments, and submit reviews. Use when the user asks about PR creation, review, comments, or granular diff analysis."},
        {"name": "github-projects", "description": "Manage GitHub Projects (Projects v2) via GitHub CLI. List projects, inspect fields, list items, add issues/PRs or draft items, and update field values. Use when the user asks about GitHub Projects boards, statuses, or moving items."},
        {"name": "azure-board", "description": "Manage Azure DevOps work items (tasks, bugs, user stories). View items assigned to you, get details, create new work items, and change status. Use when the user asks about their tasks, board, backlog, sprints, or wants to create/update work items in Azure DevOps."},
        {"name": "azure-diagnostics", "description": "Debug and troubleshoot production issues on Azure. Covers Container Apps and Function Apps diagnostics, log analysis with KQL, health checks, and common issue resolution."},
    ]

    decoys = other_skills if other_skills is not None else default_decoys

    # Add decoys that don't clash with target skill name
    for d in decoys:
        if d["name"] != skill_name:
            skills.append(f"- **{d['name']}**: {d['description']}")

    # Insert the target skill at a random-ish position (middle)
    target_entry = f"- **{skill_name}**: {skill_description}"
    mid = len(skills) // 2
    skills.insert(mid, target_entry)

    return "\n".join(skills)


def test_trigger(
    query: str,
    skill_name: str,
    skill_description: str,
    model: str | None = None,
    backend: str | None = None,
    timeout: int = 30,
    other_skills: list[dict] | None = None,
) -> bool:
    """Test whether a query triggers the skill.

    Returns True if the model decides to invoke the target skill.
    """
    if backend is None:
        backend = detect_backend()
    model = _resolve_model(model, backend)

    if backend == "claude_cli":
        # Original approach: delegate to run_eval's claude-based method
        # This is handled externally by run_eval.py for backward compat
        raise NotImplementedError("Use run_eval.run_single_query() for claude_cli backend")
    elif backend == "anthropic_api":
        return _test_trigger_anthropic_api(query, skill_name, skill_description, model, timeout, other_skills)
    elif backend == "github_models":
        return _test_trigger_github_models(query, skill_name, skill_description, model, timeout, other_skills)
    else:
        raise ValueError(f"Unknown backend: {backend}")


def _test_trigger_anthropic_api(
    query: str, skill_name: str, skill_description: str,
    model: str, timeout: int, other_skills: list[dict] | None,
) -> bool:
    """Test triggering via Anthropic Messages API with tools."""
    api_key = os.environ["ANTHROPIC_API_KEY"]
    skills_list = _build_skills_list(skill_name, skill_description, other_skills)
    system = TRIGGER_SYSTEM_PROMPT.format(skills_list=skills_list)

    body = json.dumps({
        "model": model,
        "max_tokens": 256,
        "system": system,
        "messages": [{"role": "user", "content": query}],
        "tools": [USE_SKILL_TOOL_ANTHROPIC],
        "tool_choice": {"type": "auto"},
    })

    req = urllib.request.Request(
        "https://api.anthropic.com/v1/messages",
        data=body.encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
        },
    )

    try:
        with _urlopen_with_retry(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"Warning: Anthropic API call failed: {e}", file=sys.stderr)
        return False

    return _check_tool_use_anthropic(data, skill_name)


def _test_trigger_github_models(
    query: str, skill_name: str, skill_description: str,
    model: str, timeout: int, other_skills: list[dict] | None,
) -> bool:
    """Test triggering via GitHub Models API (OpenAI-compatible) with tools."""
    token = _get_gh_token()
    if not token:
        print("Warning: Failed to get gh auth token", file=sys.stderr)
        return False

    skills_list = _build_skills_list(skill_name, skill_description, other_skills)
    system = TRIGGER_SYSTEM_PROMPT.format(skills_list=skills_list)

    body = json.dumps({
        "model": model,
        "max_tokens": 256,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": query},
        ],
        "tools": [USE_SKILL_TOOL_OPENAI],
        "tool_choice": "auto",
    })

    req = urllib.request.Request(
        "https://models.inference.ai.azure.com/chat/completions",
        data=body.encode("utf-8"),
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        },
    )

    try:
        with _urlopen_with_retry(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        print(f"Warning: GitHub Models API call failed: {e}", file=sys.stderr)
        return False

    return _check_tool_use_openai(data, skill_name)


def _check_tool_use_anthropic(response: dict, skill_name: str) -> bool:
    """Check if Anthropic response contains a tool_use for the target skill."""
    for block in response.get("content", []):
        if block.get("type") == "tool_use" and block.get("name") == "use_skill":
            tool_input = block.get("input", {})
            if skill_name in tool_input.get("skill", ""):
                return True
    return False


def _check_tool_use_openai(response: dict, skill_name: str) -> bool:
    """Check if OpenAI-compatible response contains a tool_call for the target skill."""
    for choice in response.get("choices", []):
        message = choice.get("message", {})
        tool_calls = message.get("tool_calls", [])
        for tc in tool_calls:
            if tc.get("function", {}).get("name") == "use_skill":
                args_str = tc["function"].get("arguments", "{}")
                try:
                    args = json.loads(args_str)
                except json.JSONDecodeError:
                    args = {}
                if skill_name in args.get("skill", ""):
                    return True
    return False
