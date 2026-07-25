#!/usr/bin/env python3
"""
Pipeline Generator
Scaffolds CI/CD pipeline configurations for GitHub Actions or CircleCI with
build, test, security, and deploy stages. Detects node/python/go projects to
pick sensible default commands.
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List

VALID_STAGES = ["build", "test", "security", "deploy"]


def detect_runtime(project: Path) -> str:
    if (project / "package.json").exists():
        return "node"
    if (project / "pyproject.toml").exists() or (project / "requirements.txt").exists():
        return "python"
    if (project / "go.mod").exists():
        return "go"
    return "generic"


RUNTIME_COMMANDS: Dict[str, Dict[str, List[str]]] = {
    "node": {
        "setup": ["npm ci"],
        "build": ["npm run build --if-present"],
        "test": ["npm run lint --if-present", "npm test"],
    },
    "python": {
        "setup": ["pip install -r requirements.txt"],
        "build": ["python -m compileall ."],
        "test": ["python -m ruff check .", "python -m pytest"],
    },
    "go": {
        "setup": ["go mod download"],
        "build": ["go build ./..."],
        "test": ["go vet ./...", "go test ./..."],
    },
    "generic": {
        "setup": ["echo 'add setup commands here'"],
        "build": ["echo 'add build commands here'"],
        "test": ["echo 'add test commands here'"],
    },
}

GITHUB_SETUP_STEPS = {
    "node": """      - uses: actions/setup-node@v4
        with:
          node-version: '20'
          cache: 'npm'""",
    "python": """      - uses: actions/setup-python@v5
        with:
          python-version: '3.12'
          cache: 'pip'""",
    "go": """      - uses: actions/setup-go@v5
        with:
          go-version: '1.22'""",
    "generic": "",
}

CIRCLECI_IMAGES = {
    "node": "cimg/node:20.11",
    "python": "cimg/python:3.12",
    "go": "cimg/go:1.22",
    "generic": "cimg/base:current",
}


def github_job(name: str, runtime: str, commands: List[str], needs: List[str],
               extra: str = "") -> str:
    lines = [f"  {name}:"]
    if needs:
        lines.append(f"    needs: [{', '.join(needs)}]")
    if name == "deploy":
        lines.append("    if: github.ref == 'refs/heads/main'")
    lines.append("    runs-on: ubuntu-latest")
    lines.append("    steps:")
    lines.append("      - uses: actions/checkout@v4")
    setup = GITHUB_SETUP_STEPS[runtime]
    if setup and name in ("build", "test"):
        lines.append(setup)
        for cmd in RUNTIME_COMMANDS[runtime]["setup"]:
            lines.append(f"      - run: {cmd}")
    for cmd in commands:
        lines.append(f"      - run: {cmd}")
    if extra:
        lines.append(extra)
    return "\n".join(lines)


def generate_github(stages: List[str], runtime: str) -> str:
    jobs = []
    prev: List[str] = []
    for stage in stages:
        if stage == "build":
            jobs.append(github_job("build", runtime, RUNTIME_COMMANDS[runtime]["build"], prev))
        elif stage == "test":
            jobs.append(github_job("test", runtime, RUNTIME_COMMANDS[runtime]["test"], prev))
        elif stage == "security":
            extra = """      - name: Run Trivy filesystem scan
        uses: aquasecurity/trivy-action@master
        with:
          scan-type: 'fs'
          scan-ref: '.'
          severity: 'CRITICAL,HIGH'
          exit-code: '1'"""
            jobs.append(github_job("security", runtime, [], prev, extra=extra))
        elif stage == "deploy":
            extra = """      - name: Build and push image
        uses: docker/build-push-action@v5
        with:
          push: true
          tags: ghcr.io/${{ github.repository }}:${{ github.sha }}
      - name: Deploy
        run: echo 'replace with your deploy command (e.g. aws ecs update-service / kubectl apply)'"""
            jobs.append(github_job("deploy", runtime, [], prev, extra=extra))
        prev = [stage]

    return f"""name: CI/CD Pipeline
on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
{chr(10).join(jobs)}
"""


def generate_circleci(stages: List[str], runtime: str) -> str:
    image = CIRCLECI_IMAGES[runtime]
    job_blocks = []
    workflow_jobs = []
    prev = None
    for stage in stages:
        if stage == "security":
            commands = ["echo 'add security scanner here (e.g. trivy fs .)'"]
        elif stage == "deploy":
            commands = ["echo 'replace with your deploy command'"]
        else:
            commands = RUNTIME_COMMANDS[runtime]["setup"] + RUNTIME_COMMANDS[runtime][stage]
        steps = "\n".join(f"      - run: {cmd}" for cmd in commands)
        job_blocks.append(f"""  {stage}:
    docker:
      - image: {image}
    steps:
      - checkout
{steps}""")
        if prev:
            workflow_jobs.append(f"""      - {stage}:
          requires: [{prev}]""")
        else:
            workflow_jobs.append(f"      - {stage}")
        prev = stage

    return f"""version: 2.1

jobs:
{chr(10).join(job_blocks)}

workflows:
  ci:
    jobs:
{chr(10).join(workflow_jobs)}
"""


def main():
    parser = argparse.ArgumentParser(
        description="Generate a CI/CD pipeline config for GitHub Actions or CircleCI."
    )
    parser.add_argument("target", help="Project path to scaffold the pipeline into")
    parser.add_argument("--platform", default="github", choices=["github", "circleci"],
                        help="CI platform (default: github)")
    parser.add_argument("--stages", default="build,test,deploy",
                        help=f"Comma-separated stages from: {','.join(VALID_STAGES)}")
    parser.add_argument("--force", action="store_true", help="Overwrite an existing config")
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose output")
    parser.add_argument("--json", action="store_true", help="Output results as JSON")
    parser.add_argument("--output", "-o", help="Write JSON results to this file")
    args = parser.parse_args()

    project = Path(args.target)
    if not project.is_dir():
        print(f"❌ Error: target path is not a directory: {project}", file=sys.stderr)
        sys.exit(1)

    stages = [s.strip() for s in args.stages.split(",") if s.strip()]
    invalid = [s for s in stages if s not in VALID_STAGES]
    if invalid or not stages:
        print(f"❌ Error: invalid stages {invalid or '(none)'}; "
              f"choose from {','.join(VALID_STAGES)}", file=sys.stderr)
        sys.exit(1)

    runtime = detect_runtime(project)
    if args.verbose:
        print(f"📊 Detected runtime: {runtime}")

    if args.platform == "github":
        config = generate_github(stages, runtime)
        config_path = project / ".github" / "workflows" / "ci.yml"
    else:
        config = generate_circleci(stages, runtime)
        config_path = project / ".circleci" / "config.yml"

    if config_path.exists() and not args.force:
        print(f"❌ Error: {config_path} already exists (use --force to overwrite)", file=sys.stderr)
        sys.exit(1)

    config_path.parent.mkdir(parents=True, exist_ok=True)
    config_path.write_text(config, encoding="utf-8")
    print(f"✅ Pipeline written: {config_path} (platform={args.platform}, "
          f"stages={','.join(stages)}, runtime={runtime})")

    results = {
        "status": "success",
        "platform": args.platform,
        "stages": stages,
        "runtime": runtime,
        "config_path": str(config_path),
    }
    if args.json or args.output:
        output = json.dumps(results, indent=2)
        if args.output:
            Path(args.output).write_text(output, encoding="utf-8")
            print(f"Results written to {args.output}")
        else:
            print(output)


if __name__ == "__main__":
    main()
