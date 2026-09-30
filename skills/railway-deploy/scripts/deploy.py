#!/usr/bin/env python3
"""
Railway Deploy Agent Script
Detects project type, validates readiness, and executes full deploy workflow.
Usage: python deploy.py [--project NAME] [--env ENV] [--service SERVICE] [--vars KEY=VAL ...]
"""

import subprocess
import sys
import os
import json
import argparse
import re
from pathlib import Path


# ─── Language Detection ────────────────────────────────────────────────────────

DETECTION_MAP = [
    ("Node.js",   ["package.json"]),
    ("Python",    ["requirements.txt", "Pipfile", "pyproject.toml", "setup.py"]),
    ("Go",        ["go.mod"]),
    ("Rust",      ["Cargo.toml"]),
    ("Ruby",      ["Gemfile"]),
    ("Java",      ["pom.xml", "build.gradle", "build.gradle.kts"]),
    ("PHP",       ["composer.json"]),
    ("Deno",      ["deno.json", "deno.jsonc"]),
    ("Elixir",    ["mix.exs"]),
    ("Static",    ["index.html"]),
]

def detect_language(path="."):
    files = set(os.listdir(path))
    for lang, triggers in DETECTION_MAP:
        if any(t in files for t in triggers):
            return lang
    return None

def check_railway_json(path="."):
    rj = Path(path) / "railway.json"
    pf = Path(path) / "Procfile"
    return rj.exists(), pf.exists()


# ─── Railway CLI Wrapper ────────────────────────────────────────────────────────

def run(cmd, capture=False, check=True):
    """Run a shell command, print output in real-time unless capture=True."""
    if capture:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        return result.stdout.strip(), result.returncode
    else:
        result = subprocess.run(cmd, shell=True, text=True)
        return "", result.returncode


def railway(subcmd, capture=False, check=True):
    return run(f"railway {subcmd}", capture=capture, check=check)


# ─── Auth Check ────────────────────────────────────────────────────────────────

def check_auth():
    out, code = railway("whoami", capture=True)
    if code != 0 or "not logged in" in out.lower():
        print("✗ Not logged in to Railway")
        print("  Run: railway login")
        sys.exit(1)
    print(f"✓ Authenticated: {out}")
    return out


# ─── Project Setup ─────────────────────────────────────────────────────────────

def setup_project(project_name=None, env=None):
    """Link to existing project or create new one."""
    out, code = railway("list", capture=True)
    projects = [line.strip() for line in out.splitlines() if line.strip()]

    if project_name:
        # Check if project exists
        if any(project_name.lower() in p.lower() for p in projects):
            print(f"✓ Found existing project: {project_name}")
            cmd = f"link -p '{project_name}'"
            if env:
                cmd += f" -e {env}"
            railway(cmd)
        else:
            print(f"→ Creating new project: {project_name}")
            railway(f"init -n '{project_name}'")
    else:
        # Check if already linked
        status_out, status_code = railway("status", capture=True)
        if status_code == 0 and "Project:" in status_out:
            print(f"✓ Already linked to project")
            print(status_out)
        else:
            print("→ No project linked. Available projects:")
            print(out or "  (none)")
            print("\nRun with --project <name> to specify, or `railway link` interactively")
            sys.exit(1)


# ─── Variable Management ───────────────────────────────────────────────────────

def set_variables(vars_list, service=None, env=None):
    """Set environment variables from KEY=VALUE list or .env file."""
    if not vars_list:
        return

    # Filter out empty/comment lines, don't log values
    pairs = []
    for item in vars_list:
        if "=" not in item:
            continue
        key = item.split("=", 1)[0]
        val = item.split("=", 1)[1]
        pairs.append(f'"{key}={val}"')

    if not pairs:
        return

    cmd = "variables " + " ".join(f"--set {p}" for p in pairs)
    if service:
        cmd += f" -s {service}"
    if env:
        cmd += f" -e {env}"
    cmd += " --skip-deploys"

    print(f"→ Setting {len(pairs)} environment variable(s)...")
    railway(cmd)
    print(f"✓ Variables set (values hidden for security)")


def load_env_file(env_file=".env"):
    """Parse .env file into KEY=VALUE list."""
    path = Path(env_file)
    if not path.exists():
        return []
    vars_list = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        vars_list.append(line)
    return vars_list


# ─── Deploy ────────────────────────────────────────────────────────────────────

def deploy(service=None, env=None, ci=False):
    """Run railway up and stream logs."""
    print("\n→ Deploying...")

    cmd = "up --detach"
    if service:
        cmd += f" -s {service}"
    if env:
        cmd += f" -e {env}"
    if ci:
        cmd = cmd.replace("--detach", "--ci")

    _, code = railway(cmd)
    if code != 0:
        print("✗ Deploy command failed")
        sys.exit(1)

    print("✓ Deploy initiated")
    return True


def stream_build_logs(service=None, env=None, lines=80):
    """Stream build logs after deploy."""
    print("\n→ Build logs:")
    cmd = f"logs --build -n {lines}"
    if service:
        cmd += f" -s {service}"
    if env:
        cmd += f" -e {env}"
    railway(cmd)


# ─── Domain ────────────────────────────────────────────────────────────────────

def provision_domain(service=None, port=None):
    """Provision Railway-provided domain."""
    print("\n→ Provisioning domain...")
    cmd = "domain"
    if service:
        cmd += f" -s {service}"
    if port:
        cmd += f" --port {port}"
    cmd += " --json"

    out, code = railway(cmd, capture=True)
    if code != 0:
        # Domain might already exist
        out2, _ = railway("domain", capture=True)
        print(f"✓ Domain: {out2}")
        return out2

    try:
        data = json.loads(out)
        domain = data.get("domain") or data.get("url") or out
        print(f"✓ Domain: https://{domain}")
        return domain
    except Exception:
        print(f"✓ Domain provisioned: {out}")
        return out


# ─── Verify ────────────────────────────────────────────────────────────────────

def verify_deployment(service=None, env=None):
    """Check deployment status and recent logs."""
    print("\n→ Verifying deployment...")
    cmd = "status"
    railway(cmd)

    print("\n→ Recent logs:")
    log_cmd = "logs -n 20"
    if service:
        log_cmd += f" -s {service}"
    if env:
        log_cmd += f" -e {env}"
    railway(log_cmd)


# ─── Full Deploy Workflow ──────────────────────────────────────────────────────

def full_deploy(args):
    print("═" * 60)
    print("  Railway Deploy Agent")
    print("═" * 60)

    # Step 1: Auth
    check_auth()

    # Step 2: Detect project
    lang = detect_language()
    has_railway_json, has_procfile = check_railway_json()
    print(f"\n✓ Detected language: {lang or 'Unknown (manual config needed)'}")
    if has_railway_json:
        print("✓ Found railway.json")
    if has_procfile:
        print("✓ Found Procfile")
    if not lang and not has_railway_json:
        print("⚠ No language detected and no railway.json — deploy may fail")
        print("  Create railway.json with explicit startCommand")

    # Step 3: Project setup
    print()
    setup_project(args.project, args.env)

    # Step 4: Variables
    vars_list = list(args.vars) if args.vars else []
    if args.env_file and Path(args.env_file).exists():
        vars_list += load_env_file(args.env_file)
        print(f"✓ Loaded vars from {args.env_file}")
    if vars_list:
        set_variables(vars_list, service=args.service, env=args.env)

    # Step 5: Deploy
    deploy(service=args.service, env=args.env, ci=args.ci)

    # Step 6: Build logs
    stream_build_logs(service=args.service, env=args.env, lines=100)

    # Step 7: Domain
    domain = provision_domain(service=args.service, port=args.port)

    # Step 8: Verify
    verify_deployment(service=args.service, env=args.env)

    print("\n" + "═" * 60)
    print("  Deployment Complete")
    if domain:
        print(f"  URL: https://{domain}" if not domain.startswith("http") else f"  URL: {domain}")
    print("═" * 60)


# ─── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Railway Deploy Agent")
    parser.add_argument("--project", "-p", help="Project name (create if new, link if exists)")
    parser.add_argument("--service", "-s", help="Service name")
    parser.add_argument("--env", "-e", default="production", help="Environment (default: production)")
    parser.add_argument("--vars", nargs="*", metavar="KEY=VALUE", help="Environment variables to set")
    parser.add_argument("--env-file", default=".env", help="Path to .env file (default: .env)")
    parser.add_argument("--port", help="Port for domain binding")
    parser.add_argument("--ci", action="store_true", help="CI mode (stream build logs then exit)")
    parser.add_argument("--redeploy", action="store_true", help="Redeploy without uploading new code")
    args = parser.parse_args()

    if args.redeploy:
        check_auth()
        print("→ Redeploying latest deployment...")
        railway("redeploy")
        stream_build_logs(service=args.service, env=args.env)
        verify_deployment(service=args.service, env=args.env)
    else:
        full_deploy(args)


if __name__ == "__main__":
    main()
