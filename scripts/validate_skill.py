#!/usr/bin/env python3
"""
Comprehensive skill validation script.

Validates skill structure, frontmatter, content quality, and bundled resources.
"""

import os
import sys
import re
import yaml
from pathlib import Path
from typing import List, Tuple, Dict, Any


class SkillValidator:
    """Validates Claude skills according to the Agent Skills Specification."""

    def __init__(self, skill_path: str):
        self.skill_path = Path(skill_path)
        self.errors: List[str] = []
        self.warnings: List[str] = []
        self.info: List[str] = []

    def validate(self) -> bool:
        """Run all validations. Returns True if skill is valid."""
        self.validate_structure()
        self.validate_skill_md()
        self.validate_bundled_resources()
        return len(self.errors) == 0

    def validate_structure(self):
        """Validate basic skill directory structure."""
        # Check skill directory exists
        if not self.skill_path.exists():
            self.errors.append(f"Skill directory not found: {self.skill_path}")
            return

        if not self.skill_path.is_dir():
            self.errors.append(f"Skill path is not a directory: {self.skill_path}")
            return

        # Check SKILL.md exists
        skill_md = self.skill_path / "SKILL.md"
        if not skill_md.exists():
            self.errors.append("SKILL.md is required but not found")
            return

        if not skill_md.is_file():
            self.errors.append("SKILL.md must be a file")
            return

        # Check for common bundled resource directories
        for dirname in ["scripts", "references", "assets"]:
            dirpath = self.skill_path / dirname
            if dirpath.exists():
                if not dirpath.is_dir():
                    self.warnings.append(f"{dirname} should be a directory, not a file")
                else:
                    self.info.append(f"Found {dirname}/ directory")

    def validate_skill_md(self):
        """Validate SKILL.md content and frontmatter."""
        skill_md = self.skill_path / "SKILL.md"
        if not skill_md.exists():
            return  # Already reported in validate_structure

        try:
            content = skill_md.read_text(encoding="utf-8")
        except Exception as e:
            self.errors.append(f"Failed to read SKILL.md: {e}")
            return

        # Validate frontmatter exists
        if not content.startswith("---"):
            self.errors.append("SKILL.md must start with YAML frontmatter (---)")
            return

        # Extract frontmatter and body
        parts = content.split("---", 2)
        if len(parts) < 3:
            self.errors.append("SKILL.md frontmatter not properly closed with ---")
            return

        frontmatter_text = parts[1]
        body = parts[2]

        # Parse YAML frontmatter
        try:
            frontmatter = yaml.safe_load(frontmatter_text)
        except yaml.YAMLError as e:
            self.errors.append(f"Invalid YAML frontmatter: {e}")
            return

        if not isinstance(frontmatter, dict):
            self.errors.append("Frontmatter must be a YAML object/dictionary")
            return

        self.validate_frontmatter(frontmatter)
        self.validate_body(body)

    def validate_frontmatter(self, frontmatter: Dict[str, Any]):
        """Validate frontmatter fields."""
        # Check required fields
        if "name" not in frontmatter:
            self.errors.append("Missing required field: name")
        else:
            self.validate_name(frontmatter["name"])

        if "description" not in frontmatter:
            self.errors.append("Missing required field: description")
        else:
            self.validate_description(frontmatter["description"])

        # Validate optional fields if present
        if "license" in frontmatter:
            self.info.append(f"License specified: {frontmatter['license']}")

        if "allowed-tools" in frontmatter:
            self.validate_allowed_tools(frontmatter["allowed-tools"])

        if "metadata" in frontmatter:
            if not isinstance(frontmatter["metadata"], dict):
                self.warnings.append("metadata should be a dictionary/object")
            else:
                self.info.append(f"Metadata fields: {', '.join(frontmatter['metadata'].keys())}")

    def validate_name(self, name: Any):
        """Validate skill name."""
        if not isinstance(name, str):
            self.errors.append(f"name must be a string, got {type(name).__name__}")
            return

        # Check naming convention (lowercase with hyphens)
        if not re.match(r"^[a-z0-9-]+$", name):
            self.errors.append(
                f"name '{name}' must be lowercase with hyphens only (no underscores, no uppercase)"
            )

        # Check for invalid patterns
        if name.startswith("-") or name.endswith("-"):
            self.errors.append(f"name '{name}' cannot start or end with a hyphen")

        if "--" in name:
            self.errors.append(f"name '{name}' cannot contain consecutive hyphens")

        # Check directory name matches
        dir_name = self.skill_path.name
        if name != dir_name:
            self.errors.append(
                f"name '{name}' doesn't match directory name '{dir_name}'"
            )

    def validate_description(self, description: Any):
        """Validate skill description."""
        if not isinstance(description, str):
            self.errors.append(
                f"description must be a string, got {type(description).__name__}"
            )
            return

        # Check for minimum length
        if len(description.strip()) < 20:
            self.warnings.append(
                "description seems too short (should clearly explain when to use this skill)"
            )

        # Check for maximum length (for marketplace display)
        if len(description) > 200:
            self.warnings.append(
                f"description is {len(description)} characters; consider keeping under 200 for better marketplace display"
            )

        # Check for angle brackets (can cause issues in some contexts)
        if "<" in description or ">" in description:
            self.errors.append("description cannot contain angle brackets (< or >)")

        # Check that it's somewhat descriptive
        vague_terms = ["helps", "assists", "various", "things", "stuff"]
        desc_lower = description.lower()
        if any(term in desc_lower for term in vague_terms):
            self.warnings.append(
                "description may be too vague; be specific about what the skill does and when to use it"
            )

    def validate_allowed_tools(self, allowed_tools: Any):
        """Validate allowed-tools field (Claude Code specific)."""
        if not isinstance(allowed_tools, list):
            self.warnings.append(
                f"allowed-tools should be a list, got {type(allowed_tools).__name__}"
            )
            return

        # Check for valid tool names
        known_tools = [
            "Read", "Write", "Edit", "Glob", "Grep", "Bash", "WebFetch",
            "WebSearch", "TodoWrite", "Task", "NotebookEdit"
        ]

        for tool in allowed_tools:
            if not isinstance(tool, str):
                self.warnings.append(f"allowed-tools contains non-string value: {tool}")
            elif tool not in known_tools:
                self.warnings.append(
                    f"Unknown tool '{tool}' in allowed-tools (may be valid but not recognized by this validator)"
                )

        self.info.append(f"Allowed tools: {', '.join(allowed_tools)}")

    def validate_body(self, body: str):
        """Validate SKILL.md instruction body."""
        body = body.strip()

        # Check for minimum content
        if len(body) < 100:
            self.warnings.append(
                "SKILL.md instruction body seems too short (should contain clear instructions)"
            )

        # Check for recommended sections
        body_lower = body.lower()

        # Positive indicators
        if "example" in body_lower or "```" in body:
            self.info.append("Includes examples (good practice)")

        if "error" in body_lower or "fail" in body_lower:
            self.info.append("Includes error handling guidance (good practice)")

        # Check for overly long content (should use progressive disclosure)
        word_count = len(body.split())
        if word_count > 5000:
            self.warnings.append(
                f"SKILL.md body is {word_count} words; consider moving detailed content to references/ for progressive disclosure"
            )

    def validate_bundled_resources(self):
        """Validate bundled resource directories."""
        # Validate scripts/ directory
        scripts_dir = self.skill_path / "scripts"
        if scripts_dir.exists():
            self.validate_scripts_directory(scripts_dir)

        # Validate references/ directory
        references_dir = self.skill_path / "references"
        if references_dir.exists():
            self.validate_references_directory(references_dir)

        # Validate assets/ directory
        assets_dir = self.skill_path / "assets"
        if assets_dir.exists():
            self.validate_assets_directory(assets_dir)

    def validate_scripts_directory(self, scripts_dir: Path):
        """Validate scripts directory contents."""
        scripts = list(scripts_dir.glob("*"))
        if not scripts:
            self.warnings.append("scripts/ directory is empty")
            return

        for script in scripts:
            if script.is_file():
                # Check if executable
                if not os.access(script, os.X_OK):
                    self.warnings.append(
                        f"Script {script.name} is not executable (consider chmod +x)"
                    )

                # Check for shebang
                try:
                    with open(script, "rb") as f:
                        first_line = f.readline()
                        if not first_line.startswith(b"#!"):
                            self.warnings.append(
                                f"Script {script.name} missing shebang (#!/usr/bin/env ...)"
                            )
                except Exception:
                    pass

        self.info.append(f"Found {len([s for s in scripts if s.is_file()])} script(s)")

    def validate_references_directory(self, references_dir: Path):
        """Validate references directory contents."""
        references = list(references_dir.glob("*"))
        if not references:
            self.warnings.append("references/ directory is empty")
            return

        file_count = len([r for r in references if r.is_file()])
        self.info.append(f"Found {file_count} reference file(s)")

        # Check for very large reference files
        for ref in references:
            if ref.is_file():
                size = ref.stat().st_size
                if size > 100_000:  # 100KB
                    self.info.append(
                        f"Large reference file: {ref.name} ({size / 1024:.1f}KB) - "
                        "ensure SKILL.md includes grep patterns for efficient loading"
                    )

    def validate_assets_directory(self, assets_dir: Path):
        """Validate assets directory contents."""
        assets = list(assets_dir.glob("*"))
        if not assets:
            self.warnings.append("assets/ directory is empty")
            return

        file_count = len([a for a in assets if a.is_file()])
        self.info.append(f"Found {file_count} asset file(s)")

        # Check for extremely large assets
        for asset in assets:
            if asset.is_file():
                size = asset.stat().st_size
                if size > 10_000_000:  # 10MB
                    self.warnings.append(
                        f"Very large asset file: {asset.name} ({size / 1024 / 1024:.1f}MB) - "
                        "consider if this is necessary"
                    )

    def print_results(self):
        """Print validation results."""
        print(f"\n{'=' * 60}")
        print(f"Skill Validation Results: {self.skill_path.name}")
        print(f"{'=' * 60}\n")

        if self.errors:
            print(f"❌ ERRORS ({len(self.errors)}):")
            for error in self.errors:
                print(f"   • {error}")
            print()

        if self.warnings:
            print(f"⚠️  WARNINGS ({len(self.warnings)}):")
            for warning in self.warnings:
                print(f"   • {warning}")
            print()

        if self.info:
            print(f"ℹ️  INFO ({len(self.info)}):")
            for info in self.info:
                print(f"   • {info}")
            print()

        if not self.errors:
            print("✅ Skill validation PASSED")
            print()
            if self.warnings:
                print("Note: Warnings are suggestions for improvement but don't prevent usage.")
        else:
            print("❌ Skill validation FAILED")
            print("Please fix the errors above before using this skill.")

        print()


def main():
    """Main entry point."""
    if len(sys.argv) != 2:
        print("Usage: python validate_skill.py <skill-directory>")
        print()
        print("Example:")
        print("  python validate_skill.py ./my-skill/")
        print("  python validate_skill.py /path/to/skills/my-skill/")
        sys.exit(1)

    skill_path = sys.argv[1]

    validator = SkillValidator(skill_path)
    is_valid = validator.validate()
    validator.print_results()

    sys.exit(0 if is_valid else 1)


if __name__ == "__main__":
    main()
