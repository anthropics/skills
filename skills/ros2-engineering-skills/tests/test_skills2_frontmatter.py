"""Tests for Skills 2.0 frontmatter — validates SKILL.md metadata completeness.

These tests ensure the skill conforms to Skills 2.0 requirements:
1. Frontmatter has all required fields
2. context: fork is declared
3. classification is valid
4. version follows semver
5. hooks are properly declared
6. evals are properly structured
"""

import os
import re

import yaml


SKILL_ROOT = os.path.join(os.path.dirname(__file__), '..')
SKILL_MD = os.path.join(SKILL_ROOT, 'SKILL.md')


def _parse_frontmatter(filepath):
    """Extract YAML frontmatter from a markdown file."""
    with open(filepath, 'r') as fh:
        content = fh.read()
    match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)
    assert match is not None, 'SKILL.md must start with YAML frontmatter (---)'
    return yaml.safe_load(match.group(1))


class TestSkills2FrontmatterStructure:
    """Validate that SKILL.md frontmatter contains all Skills 2.0 fields."""

    def setup_method(self):
        self.fm = _parse_frontmatter(SKILL_MD)

    def test_has_name(self):
        assert 'name' in self.fm
        assert isinstance(self.fm['name'], str)
        assert len(self.fm['name']) > 0

    def test_has_description(self):
        assert 'description' in self.fm
        assert isinstance(self.fm['description'], str)
        assert len(self.fm['description']) > 0

    def test_has_context_fork(self):
        assert 'context' in self.fm, 'Skills 2.0 requires context field'
        assert self.fm['context'] == 'fork', 'context must be "fork" for isolated execution'

    def test_has_classification(self):
        assert 'classification' in self.fm, 'Skills 2.0 requires classification field'
        valid_types = {'workflow', 'capability', 'hybrid'}
        assert self.fm['classification'] in valid_types, (
            f'classification must be one of {valid_types}, '
            f'got: {self.fm["classification"]}'
        )

    def test_has_version(self):
        assert 'version' in self.fm, 'Skills 2.0 requires version field'
        version = self.fm['version']
        assert re.match(r'^\d+\.\d+\.\d+$', str(version)), (
            f'version must follow semver (X.Y.Z), got: {version}'
        )

    def test_has_deprecation_risk(self):
        assert 'deprecation-risk' in self.fm, (
            'Skills 2.0 requires deprecation-risk field'
        )
        valid_levels = {'none', 'low', 'medium', 'high'}
        assert self.fm['deprecation-risk'] in valid_levels, (
            f'deprecation-risk must be one of {valid_levels}, '
            f'got: {self.fm["deprecation-risk"]}'
        )


class TestSkills2FrontmatterHooks:
    """Validate that hooks are properly declared in frontmatter."""

    def setup_method(self):
        self.fm = _parse_frontmatter(SKILL_MD)

    def test_has_hooks(self):
        assert 'hooks' in self.fm, 'Skills 2.0 requires hooks field'
        assert isinstance(self.fm['hooks'], dict)

    def test_hooks_have_valid_events(self):
        hooks = self.fm['hooks']
        valid_events = {
            'PreToolUse', 'PostToolUse', 'Stop',
            'NotificationArrived', 'SubagentStop',
        }
        for event in hooks:
            assert event in valid_events, (
                f'Hook event "{event}" is not a valid Skills 2.0 hook event. '
                f'Valid events: {valid_events}'
            )

    def test_stop_hook_exists(self):
        hooks = self.fm['hooks']
        assert 'Stop' in hooks, 'Must have a Stop hook for post-execution validation'
        stop_hooks = hooks['Stop']
        assert isinstance(stop_hooks, list)
        assert len(stop_hooks) > 0

    def test_hook_entries_have_required_fields(self):
        hooks = self.fm['hooks']
        for event, entries in hooks.items():
            for i, entry in enumerate(entries):
                assert 'type' in entry, (
                    f'Hook {event}[{i}] missing "type"'
                )
                assert entry['type'] in ('command', 'script'), (
                    f'Hook {event}[{i}] type must be "command" or "script"'
                )
                assert 'command' in entry, (
                    f'Hook {event}[{i}] missing "command"'
                )
                assert isinstance(entry['command'], str)

    def test_hook_commands_reference_existing_scripts(self):
        hooks = self.fm['hooks']
        for event, entries in hooks.items():
            for i, entry in enumerate(entries):
                cmd = entry['command']
                # Extract the script path from the command
                # Handle ${SKILL_ROOT} or ${CLAUDE_PLUGIN_ROOT} variables
                script_path = cmd.replace(
                    '${SKILL_ROOT}', SKILL_ROOT
                ).replace(
                    '${CLAUDE_PLUGIN_ROOT}', SKILL_ROOT
                )
                # Extract the actual file path (after python3/node command)
                parts = script_path.split()
                if len(parts) >= 2:
                    script_file = parts[1]
                    assert os.path.isfile(script_file), (
                        f'Hook {event}[{i}] references non-existent script: '
                        f'{script_file}'
                    )

    def test_hooks_have_timeout(self):
        hooks = self.fm['hooks']
        for event, entries in hooks.items():
            for i, entry in enumerate(entries):
                assert 'timeout' in entry, (
                    f'Hook {event}[{i}] should have a timeout'
                )
                assert isinstance(entry['timeout'], (int, float))
                assert entry['timeout'] > 0


class TestSkills2FrontmatterEvals:
    """Validate that evals are properly declared in frontmatter."""

    def setup_method(self):
        self.fm = _parse_frontmatter(SKILL_MD)

    def test_has_evals(self):
        assert 'evals' in self.fm, 'Skills 2.0 requires evals field'
        assert isinstance(self.fm['evals'], list)
        assert len(self.fm['evals']) > 0

    def test_evals_have_required_fields(self):
        for i, ev in enumerate(self.fm['evals']):
            assert 'name' in ev, f'Eval {i} missing "name"'
            assert 'prompt' in ev, f'Eval {i} missing "prompt"'
            assert 'expected' in ev, f'Eval {i} missing "expected"'
            assert 'criteria' in ev, f'Eval {i} missing "criteria"'

    def test_eval_names_are_unique(self):
        names = [ev['name'] for ev in self.fm['evals']]
        assert len(names) == len(set(names)), (
            f'Eval names must be unique, found duplicates: '
            f'{[n for n in names if names.count(n) > 1]}'
        )

    def test_eval_prompt_files_exist(self):
        for ev in self.fm['evals']:
            prompt_path = os.path.join(SKILL_ROOT, ev['prompt'])
            assert os.path.isfile(prompt_path), (
                f'Eval "{ev["name"]}" prompt file not found: {prompt_path}'
            )

    def test_eval_expected_files_exist(self):
        for ev in self.fm['evals']:
            expected_path = os.path.join(SKILL_ROOT, ev['expected'])
            assert os.path.isfile(expected_path), (
                f'Eval "{ev["name"]}" expected file not found: {expected_path}'
            )

    def test_eval_criteria_are_non_empty(self):
        for ev in self.fm['evals']:
            assert len(ev['criteria']) > 0, (
                f'Eval "{ev["name"]}" must have at least one criterion'
            )

    def test_eval_timeouts_are_positive(self):
        for ev in self.fm['evals']:
            assert 'timeout' in ev, (
                f'Eval "{ev["name"]}" should have a timeout'
            )
            assert isinstance(ev['timeout'], (int, float))
            assert ev['timeout'] > 0

    def test_eval_prompt_files_are_non_empty(self):
        for ev in self.fm['evals']:
            prompt_path = os.path.join(SKILL_ROOT, ev['prompt'])
            with open(prompt_path, 'r') as fh:
                content = fh.read().strip()
            assert len(content) > 50, (
                f'Eval "{ev["name"]}" prompt file is too short '
                f'({len(content)} chars)'
            )

    def test_eval_expected_files_are_non_empty(self):
        for ev in self.fm['evals']:
            expected_path = os.path.join(SKILL_ROOT, ev['expected'])
            with open(expected_path, 'r') as fh:
                content = fh.read().strip()
            assert len(content) > 50, (
                f'Eval "{ev["name"]}" expected file is too short '
                f'({len(content)} chars)'
            )


class TestSkills2ClassificationConsistency:
    """Validate that classification and deprecation-risk are consistent."""

    def setup_method(self):
        self.fm = _parse_frontmatter(SKILL_MD)

    def test_workflow_has_no_deprecation_risk(self):
        """Workflow skills should have deprecation-risk: none."""
        if self.fm['classification'] == 'workflow':
            assert self.fm['deprecation-risk'] == 'none', (
                'Workflow skills should have deprecation-risk: none'
            )

    def test_capability_has_deprecation_risk(self):
        """Capability skills should have deprecation-risk: medium or high."""
        if self.fm['classification'] == 'capability':
            assert self.fm['deprecation-risk'] in ('medium', 'high'), (
                'Capability skills should have deprecation-risk: medium or high'
            )

    def test_hybrid_has_low_deprecation_risk(self):
        """Hybrid skills should have deprecation-risk: low."""
        if self.fm['classification'] == 'hybrid':
            assert self.fm['deprecation-risk'] == 'low', (
                'Hybrid skills should have deprecation-risk: low'
            )
