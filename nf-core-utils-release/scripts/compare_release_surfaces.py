#!/usr/bin/env python3
"""Compare nf-core-utils versions on GitHub Releases and the Nextflow Plugin Registry."""
import json
import subprocess
import urllib.request

PLUGIN = "nf-core-utils"
REGISTRY_URL = f"https://registry.nextflow.io/api/v1/plugins/{PLUGIN}"

release_lines = subprocess.check_output(["gh", "release", "list", "--limit", "50"], text=True).splitlines()
github_versions = [line.split("\t")[2] for line in release_lines if line.strip()]
with urllib.request.urlopen(REGISTRY_URL) as response:
    registry_data = json.load(response)
registry_versions = [release["version"] for release in registry_data["plugin"]["releases"]]

print("GitHub:", ", ".join(github_versions) or "none")
print("Registry:", ", ".join(registry_versions) or "none")
print("Missing from registry:", ", ".join(sorted(set(github_versions) - set(registry_versions))) or "none")
print("Missing from GitHub:", ", ".join(sorted(set(registry_versions) - set(github_versions))) or "none")
