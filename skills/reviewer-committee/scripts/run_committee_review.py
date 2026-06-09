#!/usr/bin/env python3
"""
Committee Review Runner

Runs Codex (gpt-5.4) and Gemini (gemini-3.1-pro-preview) code reviews in parallel
and writes COMMITTEE_REVIEW.md to the output directory.

Usage:
    python run_committee_review.py [--mode uncommitted|base|commit|files]
                                   [--param <branch|sha|"file1 file2">]
                                   [--output-dir <dir>]
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path


GEMINI_REVIEW_PROMPT = """You are a senior code reviewer. Review the following code changes carefully and provide structured feedback.

Structure your response EXACTLY as follows (keep these exact section headers):

## Strengths
What is done well: good architecture decisions, clean code, solid test coverage, clear naming, etc.

## Critical Issues
Blocking problems that MUST be fixed before this code ships: bugs, security vulnerabilities, data loss risks, broken logic, crashes.
If none: write "None identified."

## Important Issues
Significant problems that SHOULD be fixed: correctness concerns, design flaws, missing error handling, performance problems.
If none: write "None identified."

## Minor Issues
Nice-to-have improvements: style, naming conventions, documentation gaps, minor optimizations.
If none: write "None identified."

## Overall Assessment
A brief paragraph summarizing the quality and key concerns.

**Recommendation:** [Approve | Approve with Changes | Needs Work | Major Revisions Required]

---
Code changes to review:
"""


def get_git_diff(mode: str, param: str, project_dir: str = ".") -> str:
    """Retrieve the code content to review based on mode.

    All git commands and file paths are resolved relative to project_dir.
    """
    project_path = Path(project_dir).resolve()
    try:
        if mode == "uncommitted":
            staged = subprocess.run(
                ["git", "diff", "--cached"],
                capture_output=True, text=True, cwd=project_path
            ).stdout
            unstaged = subprocess.run(
                ["git", "diff"],
                capture_output=True, text=True, cwd=project_path
            ).stdout
            return staged + unstaged

        elif mode == "base":
            return subprocess.run(
                ["git", "diff", f"{param}...HEAD"],
                capture_output=True, text=True, cwd=project_path
            ).stdout

        elif mode == "commit":
            return subprocess.run(
                ["git", "show", param],
                capture_output=True, text=True, cwd=project_path
            ).stdout

        elif mode == "files":
            content = ""
            for filepath in param.split():
                # Resolve relative to project_dir
                p = (project_path / filepath) if not Path(filepath).is_absolute() else Path(filepath)
                if p.exists():
                    content += f"\n### {filepath}\n```\n{p.read_text()}\n```\n"
                else:
                    content += f"\n### {filepath}\n(file not found: {p})\n"
            return content

    except Exception as e:
        return f"(error retrieving diff: {e})"

    return ""


def run_codex_review(mode: str, param: str, file_content: str = "", project_dir: str = ".") -> tuple[str, str]:
    """Run codex review. Returns (output, error_msg).

    For git-based modes (uncommitted/base/commit), uses native codex review flags.
    For files mode, pipes the file content as the review prompt via stdin.
    """
    try:
        if mode == "files":
            # codex review doesn't have a --files flag; pipe content as the prompt via stdin
            if not file_content.strip():
                return "", "No file content to review."
            prompt = (
                "Please review the following source files for bugs, design issues, "
                "and improvements. Provide structured feedback with sections: "
                "Strengths, Critical Issues, Important Issues, Minor Issues, Overall Assessment.\n\n"
                + file_content
            )
            result = subprocess.run(
                ["codex", "review", "-c", 'model="gpt-5.4"', "-"],
                input=prompt,
                capture_output=True,
                text=True,
                timeout=600,
                cwd=project_dir,
            )
        else:
            cmd = ["codex", "review", "-c", 'model="gpt-5.4"']
            if mode == "uncommitted":
                cmd.append("--uncommitted")
            elif mode == "base":
                cmd.extend(["--base", param])
            elif mode == "commit":
                cmd.extend(["--commit", param])
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=600, cwd=project_dir)

        output = result.stdout.strip()
        if result.returncode != 0 and not output:
            return "", result.stderr.strip() or f"Exit code {result.returncode}"
        if result.stderr.strip():
            output = output + "\n" + result.stderr.strip() if output else result.stderr.strip()
        return output, ""
    except subprocess.TimeoutExpired:
        return "", "Codex review timed out after 10 minutes. Try a smaller set of files."
    except FileNotFoundError:
        return "", "codex CLI not found. Install via: npm install -g @openai/codex"
    except Exception as e:
        return "", str(e)


def run_gemini_review(diff_content: str, project_dir: str = ".") -> tuple[str, str]:
    """Run gemini review with diff piped via stdin. Returns (output, error_msg).

    Uses --sandbox for isolation. The cwd is set to project_dir so Gemini reads
    the correct repo's context, not the caller's directory.
    """
    if not diff_content.strip():
        return "", "No diff content to review."

    try:
        result = subprocess.run(
            [
                "gemini",
                "-m", "gemini-3.1-pro-preview",
                "-p", GEMINI_REVIEW_PROMPT,
                "--sandbox",                 # sandbox isolation
                "--output-format", "text",
            ],
            input=diff_content,
            capture_output=True,
            text=True,
            timeout=600,
            cwd=project_dir,
        )
        output = result.stdout.strip()
        if result.returncode != 0 and not output:
            return "", result.stderr.strip() or f"Exit code {result.returncode}"
        return output, ""
    except subprocess.TimeoutExpired:
        return "", "Gemini review timed out after 10 minutes. Try a smaller set of files."
    except FileNotFoundError:
        return "", "gemini CLI not found. Install via: npm install -g @google/gemini-cli"
    except Exception as e:
        return "", str(e)


def describe_subject(mode: str, param: str) -> str:
    if mode == "uncommitted":
        return "Uncommitted changes (staged + unstaged)"
    elif mode == "base":
        return f"Changes vs `{param}`"
    elif mode == "commit":
        return f"Commit `{param}`"
    elif mode == "files":
        return f"Files: {param}"
    return "Code review"


def write_committee_review(
    output_dir: str,
    codex_output: str,
    codex_error: str,
    gemini_output: str,
    gemini_error: str,
    mode: str,
    param: str,
) -> str:
    """Write COMMITTEE_REVIEW.md and return its path."""
    subject = describe_subject(mode, param)
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    codex_section = codex_output if codex_output else f"> Review unavailable.\n> Error: {codex_error}"
    gemini_section = gemini_output if gemini_output else f"> Review unavailable.\n> Error: {gemini_error}"

    content = f"""# Committee Review Report

**Subject:** {subject}
**Date:** {timestamp}
**Panel:** GPT-5.4 (Codex CLI) · Gemini-3.1-Pro-Preview (Gemini CLI)

---

## Codex Review (GPT-5.4)

{codex_section}

---

## Gemini Review (Gemini-3.1-Pro-Preview)

{gemini_section}

---

## How to Process This Review

Issues flagged by **both reviewers** carry the highest confidence — prioritize those.

**Severity guide:**
- **Critical** — fix before doing anything else (blocking bugs, security holes, data loss)
- **Important** — fix before merging (correctness, design, missing error handling)
- **Minor** — address if time permits (style, naming, docs)

**Before implementing any suggestion:**
1. Verify it applies to your actual codebase — reviewers lack full context
2. Check whether it breaks existing functionality
3. Push back with technical reasoning if the suggestion is wrong for this project
"""

    output_path = Path(output_dir) / "COMMITTEE_REVIEW.md"
    output_path.write_text(content)
    return str(output_path)


def main():
    parser = argparse.ArgumentParser(
        description="Run parallel multi-model committee code review"
    )
    parser.add_argument(
        "--mode",
        choices=["uncommitted", "base", "commit", "files"],
        default="uncommitted",
        help="What to review",
    )
    parser.add_argument(
        "--param",
        default="",
        help="Branch name (base mode), commit SHA (commit mode), or space-separated files (files mode)",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Directory to write COMMITTEE_REVIEW.md (default: same as --project-dir)",
    )
    parser.add_argument(
        "--project-dir",
        default=".",
        help="Root of the project to review — CLIs run with this as cwd so they pick up the right context (default: current directory)",
    )
    args = parser.parse_args()

    # Default output-dir to project-dir so COMMITTEE_REVIEW.md lands in the repo
    if args.output_dir is None:
        args.output_dir = args.project_dir

    subject = describe_subject(args.mode, args.param)
    print(f"Committee Review: {subject}")
    print("Running Codex (gpt-5.4) and Gemini (gemini-3.1-pro-preview) in parallel...")
    print()

    # Get diff content — resolved relative to project_dir
    diff_content = get_git_diff(args.mode, args.param, args.project_dir)
    if not diff_content.strip() and args.mode != "files":
        print("Warning: No diff content found. Do you have staged or unstaged changes?")
        print("Continuing anyway — reviewers will report empty input.")

    with ThreadPoolExecutor(max_workers=2) as executor:
        codex_future = executor.submit(run_codex_review, args.mode, args.param, diff_content, args.project_dir)
        gemini_future = executor.submit(run_gemini_review, diff_content, args.project_dir)

        for future in as_completed([codex_future, gemini_future]):
            if future is codex_future:
                label = "Codex"
            else:
                label = "Gemini"
            _, err = future.result()
            if err:
                print(f"  {label}: error - {err}")
            else:
                print(f"  {label}: done")

    codex_output, codex_error = codex_future.result()
    gemini_output, gemini_error = gemini_future.result()

    output_path = write_committee_review(
        args.output_dir,
        codex_output,
        codex_error,
        gemini_output,
        gemini_error,
        args.mode,
        args.param,
    )

    print(f"\nCOMMITTEE_REVIEW.md written to: {output_path}")

    # Return non-zero if both reviewers failed
    if codex_error and gemini_error:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
