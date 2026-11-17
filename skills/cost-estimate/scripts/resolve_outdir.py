#!/usr/bin/env python3
"""Derive the output directory for cost-estimate artifacts.

Prints a platform-appropriate, project-scoped temp directory, creating it
if needed. Never writes inside the user's working tree — reports can
contain sensitive numbers (rates, costs, team composition) that should
not land in a git commit by accident.

Typical paths (all use forward slashes in this skill's authored docs —
Windows clients display them with backslashes, but pathlib handles the
translation transparently):
  Linux   → /tmp/cost-estimate/<project>/
  macOS   → /var/folders/.../T/cost-estimate/<project>/
  Windows → %TEMP%/cost-estimate/<project>/
"""
import os
import pathlib
import tempfile

proj = pathlib.Path(os.getcwd()).name or "unknown"
out = pathlib.Path(tempfile.gettempdir()) / "cost-estimate" / proj
out.mkdir(parents=True, exist_ok=True)
print(out)
