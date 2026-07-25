#!/usr/bin/env python3
"""
Query multiple LLMs (Gemini and ChatGPT) for their perspectives on a given prompt.

Priority order:
1. CLI tools (gemini-cli, codex) - preferred for token efficiency
2. API calls - fallback when CLIs are unavailable

Uses environment variables for API keys (only needed if CLI fallback is required).
"""

import os
import sys
import json
import shutil
import subprocess
from typing import Dict, Optional, Tuple
import requests


def load_env_file(env_path: str = ".env") -> Dict[str, str]:
    """Load environment variables from .env file."""
    env_vars = {}
    if not os.path.exists(env_path):
        return env_vars

    with open(env_path, "r") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, value = line.split("=", 1)
                env_vars[key.strip()] = value.strip().strip('"').strip("'")

    return env_vars


def is_cli_available(cli_name: str) -> bool:
    """Check if a CLI tool is available in the system PATH."""
    return shutil.which(cli_name) is not None


def query_gemini_cli(prompt: str, timeout: int = 60) -> Tuple[bool, str]:
    """
    Query Gemini using gemini-cli.
    Returns (success, response_or_error).
    """
    try:
        result = subprocess.run(
            ["gemini", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode == 0:
            return True, result.stdout.strip()
        else:
            return False, f"gemini-cli error: {result.stderr.strip()}"
    except subprocess.TimeoutExpired:
        return False, "gemini-cli timed out"
    except Exception as e:
        return False, f"gemini-cli exception: {str(e)}"


def query_codex_cli(prompt: str, timeout: int = 60) -> Tuple[bool, str]:
    """
    Query ChatGPT using OpenAI's codex CLI.
    Returns (success, response_or_error).
    """
    try:
        result = subprocess.run(
            ["codex", "-p", prompt],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode == 0:
            return True, result.stdout.strip()
        else:
            return False, f"codex error: {result.stderr.strip()}"
    except subprocess.TimeoutExpired:
        return False, "codex timed out"
    except Exception as e:
        return False, f"codex exception: {str(e)}"


def query_openai(prompt: str, api_key: str, model: str = "gpt-5-nano") -> Optional[str]:
    """Query OpenAI's ChatGPT API."""
    try:
        response = requests.post(
            "https://api.openai.com/v1/chat/completions",
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
            },
            json={
                "model": model,
                "messages": [{"role": "user", "content": prompt}],
                "max_tokens": 2000,
                "temperature": 0.7,
            },
            timeout=30,
        )
        response.raise_for_status()
        return response.json()["choices"][0]["message"]["content"]
    except Exception as e:
        return f"Error querying ChatGPT ({model}): {str(e)}"


def query_gemini(
    prompt: str, api_key: str, model: str = "gemini-3-flash-preview"
) -> Optional[str]:
    """Query Google's Gemini API."""
    try:
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={api_key}"
        response = requests.post(
            url,
            headers={"Content-Type": "application/json"},
            json={
                "contents": [{"parts": [{"text": prompt}]}],
                "generationConfig": {"temperature": 0.7, "maxOutputTokens": 2000},
            },
            timeout=30,
        )
        response.raise_for_status()
        data = response.json()
        return data["candidates"][0]["content"]["parts"][0]["text"]
    except Exception as e:
        return f"Error querying Gemini ({model}): {str(e)}"


def main():
    if len(sys.argv) < 2:
        print(
            json.dumps(
                {
                    "error": "Usage: query_llms.py <prompt>",
                    "chatgpt": None,
                    "gemini": None,
                }
            )
        )
        sys.exit(1)

    prompt = " ".join(sys.argv[1:])

    # Load environment variables
    env_vars = load_env_file()
    openai_key = env_vars.get("OPENAI_API_KEY") or os.environ.get("OPENAI_API_KEY")
    gemini_key = env_vars.get("GEMINI_API_KEY") or os.environ.get("GEMINI_API_KEY")

    # Get model configuration (with defaults)
    openai_model = (
        env_vars.get("OPENAI_MODEL") or os.environ.get("OPENAI_MODEL") or "gpt-5-nano"
    )
    gemini_model = (
        env_vars.get("GEMINI_MODEL")
        or os.environ.get("GEMINI_MODEL")
        or "gemini-3-flash-preview"
    )

    # Check CLI availability
    gemini_cli_available = is_cli_available("gemini")
    codex_cli_available = is_cli_available("codex")

    # Query ChatGPT: try codex CLI first, fallback to API
    chatgpt_response = None
    chatgpt_source = None

    if codex_cli_available:
        success, response = query_codex_cli(prompt)
        if success:
            chatgpt_response = response
            chatgpt_source = "codex-cli"

    if chatgpt_response is None:
        if openai_key:
            chatgpt_response = query_openai(prompt, openai_key, openai_model)
            chatgpt_source = f"api ({openai_model})"
        else:
            chatgpt_response = "Error: codex CLI not available and OPENAI_API_KEY not found"
            chatgpt_source = "none"

    # Query Gemini: try gemini-cli first, fallback to API
    gemini_response = None
    gemini_source = None

    if gemini_cli_available:
        success, response = query_gemini_cli(prompt)
        if success:
            gemini_response = response
            gemini_source = "gemini-cli"

    if gemini_response is None:
        if gemini_key:
            gemini_response = query_gemini(prompt, gemini_key, gemini_model)
            gemini_source = f"api ({gemini_model})"
        else:
            gemini_response = "Error: gemini CLI not available and GEMINI_API_KEY not found"
            gemini_source = "none"

    # Output as JSON
    result = {
        "prompt": prompt,
        "chatgpt": {"model": openai_model, "source": chatgpt_source, "response": chatgpt_response},
        "gemini": {"model": gemini_model, "source": gemini_source, "response": gemini_response},
    }

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
