"""
TDD workflow guidance module.

Provides step-by-step guidance through red-green-refactor cycles with validation.
"""

from typing import Dict, List, Any, Optional
from enum import Enum


class TDDPhase(Enum):
    """TDD cycle phases."""
    RED = "red"  # Write failing test
    GREEN = "green"  # Make test pass
    REFACTOR = "refactor"  # Improve code


class WorkflowState(Enum):
    """Current state of TDD workflow."""
    INITIAL = "initial"
    TEST_WRITTEN = "test_written"
    TEST_FAILING = "test_failing"
    TEST_PASSING = "test_passing"
    CODE_REFACTORED = "code_refactored"


class TDDWorkflow:
    """Guide users through TDD red-green-refactor workflow."""

    def __init__(self):
        """Initialize TDD workflow guide."""
        self.current_phase = TDDPhase.RED
        self.state = WorkflowState.INITIAL
        self.history = []

    def start_cycle(self, requirement: str) -> Dict[str, Any]:
        """
        Start a new TDD cycle.

        Args:
            requirement: User story or requirement to implement

        Returns:
            Guidance for RED phase
        """
        self.current_phase = TDDPhase.RED
        self.state = WorkflowState.INITIAL

        return {
            'phase': 'RED',
            'instruction': 'Write a failing test for the requirement',
            'requirement': requirement,
            'checklist': [
                'Write test that describes desired behavior',
                'Test should fail when run (no implementation yet)',
                'Test name clearly describes what is being tested',
                'Test has clear arrange-act-assert structure'
            ],
            'tips': [
                'Focus on behavior, not implementation',
                'Start with simplest test case',
                'Test should be specific and focused'
            ]
        }

    def validate_red_phase(
        self,
        test_code: str,
        test_result: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Validate RED phase completion.

        Args:
            test_code: The test code written
            test_result: Test execution result (optional)

        Returns:
            Validation result and next steps
        """
        validations = []

        # Check test exists
        if not test_code or len(test_code.strip()) < 10:
            validations.append({
                'valid': False,
                'message': 'No test code provided'
            })
        else:
            validations.append({
                'valid': True,
                'message': 'Test code provided'
            })

        # Check for assertions
        has_assertion = any(keyword in test_code.lower()
                           for keyword in ['assert', 'expect', 'should'])
        validations.append({
            'valid': has_assertion,
            'message': 'Contains assertions' if has_assertion else 'Missing assertions'
        })

        # Check test result if provided
        if test_result:
            test_failed = test_result.get('status') == 'failed'
            validations.append({
                'valid': test_failed,
                'message': 'Test fails as expected' if test_failed else 'Test should fail in RED phase'
            })

        all_valid = all(v['valid'] for v in validations)

        if all_valid:
            self.state = WorkflowState.TEST_FAILING
            self.current_phase = TDDPhase.GREEN
            return {
                'phase_complete': True,
                'next_phase': 'GREEN',
                'validations': validations,
                'instruction': 'Write minimal code to make the test pass'
            }
        else:
            return {
                'phase_complete': False,
                'current_phase': 'RED',
                'validations': validations,
                'instruction': 'Address validation issues before proceeding'
            }

    def validate_green_phase(
        self,
        implementation_code: str,
        test_result: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Validate GREEN phase completion.

        Args:
            implementation_code: The implementation code
            test_result: Test execution result

        Returns:
            Validation result and next steps
        """
        validations = []

        # Check implementation exists
        if not implementation_code or len(implementation_code.strip()) < 5:
            validations.append({
                'valid': False,
                'message': 'No implementation code provided'
            })
        else:
            validations.append({
                'valid': True,
                'message': 'Implementation code provided'
            })

        # Check test now passes
        test_passed = test_result.get('status') == 'passed'
        validations.append({
            'valid': test_passed,
            'message': 'Test passes' if test_passed else 'Test still failing'
        })

        # Check for minimal implementation (heuristic)
        is_minimal = self._check_minimal_implementation(implementation_code)
        validations.append({
            'valid': is_minimal,
            'message': 'Implementation appears minimal' if is_minimal
                      else 'Implementation may be over-engineered'
        })

        all_valid = all(v['valid'] for v in validations)

        if all_valid:
            self.state = WorkflowState.TEST_PASSING
            self.current_phase = TDDPhase.REFACTOR
            return {
                'phase_complete': True,
                'next_phase': 'REFACTOR',
                'validations': validations,
                'instruction': 'Refactor code while keeping tests green',
                'refactoring_suggestions': self._suggest_refactorings(implementation_code)
            }
        else:
            return {
                'phase_complete': False,
                'current_phase': 'GREEN',
                'validations': validations,
                'instruction': 'Make the test pass before refactoring'
            }

    def validate_refactor_phase(
        self,
        original_code: str,
        refactored_code: str,
        test_result: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Validate REFACTOR phase completion.

        Args:
            original_code: Original implementation
            refactored_code: Refactored implementation
            test_result: Test execution result after refactoring

        Returns:
            Validation result and cycle completion status
        """
        validations = []

        # Check tests still pass
        test_passed = test_result.get('status') == 'passed'
        validations.append({
            'valid': test_passed,
            'message': 'Tests still pass after refactoring' if test_passed
                      else 'Tests broken by refactoring'
        })

        # Check code was actually refactored
        code_changed = original_code != refactored_code
        validations.append({
            'valid': code_changed,
            'message': 'Code was refactored' if code_changed
                      else 'No refactoring applied (optional)'
        })

        # Check code quality improved
        quality_improved = self._check_quality_improvement(original_code, refactored_code)
        if code_changed:
            validations.append({
                'valid': quality_improved,
                'message': 'Code quality improved' if quality_improved
                          else 'Consider further refactoring for better quality'
            })

        all_valid = all(v['valid'] for v in validations if v.get('valid') is not None)

        if all_valid:
            self.state = WorkflowState.CODE_REFACTORED
            self.history.append({
                'cycle_complete': True,
                'final_state': self.state
            })
            return {
                'phase_complete': True,
                'cycle_complete': True,
                'validations': validations,
                'message': 'TDD cycle complete! Ready for next requirement.',
                'next_steps': [
                    'Commit your changes',
                    'Start next TDD cycle with new requirement',
                    'Or add more test cases for current feature'
                ]
            }
        else:
            return {
                'phase_complete': False,
                'current_phase': 'REFACTOR',
                'validations': validations,
                'instruction': 'Ensure tests still pass after refactoring'
            }

    def _check_minimal_implementation(self, code: str) -> bool:
        """Check if implementation is minimal (heuristic)."""
        # Simple heuristics:
        # - Not too long (< 50 lines for unit tests)
        # - Not too complex (few nested structures)

        lines = code.split('\n')
        non_empty_lines = [line for line in lines if line.strip() and not line.strip().startswith('#')]

        # Check length
        if len(non_empty_lines) > 50:
            return False

        # Check nesting depth (simplified)
        max_depth = 0
        current_depth = 0
        for line in lines:
            stripped = line.lstrip()
            if stripped:
                indent = len(line) - len(stripped)
                depth = indent // 4  # Assuming 4-space indent
                max_depth = max(max_depth, depth)

        # Max nesting of 3 levels for simple implementation
        return max_depth <= 3

    def _check_quality_improvement(self, original: str, refactored: str) -> bool:
        """Check if refactoring improved code quality."""
        # Simple heuristics:
        # - Reduced duplication
        # - Better naming
        # - Simpler structure

        # Check for reduced duplication (basic check)
        original_lines = set(line.strip() for line in original.split('\n') if line.strip())
        refactored_lines = set(line.strip() for line in refactored.split('\n') if line.strip())

        # If unique lines increased proportionally, likely extracted duplicates
        if len(refactored_lines) > len(original_lines):
            return True

        # Check for better naming (longer, more descriptive names)
        original_avg_identifier_length = self._avg_identifier_length(original)
        refactored_avg_identifier_length = self._avg_identifier_length(refactored)

        if refactored_avg_identifier_length > original_avg_identifier_length:
            return True

        # If no clear improvement detected, assume refactoring was beneficial
        return True

    def _avg_identifier_length(self, code: str) -> float:
        """Calculate average identifier length (proxy for naming quality)."""
        import re
        identifiers = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', code)

        # Filter out keywords
        keywords = {'if', 'else', 'for', 'while', 'def', 'class', 'return', 'import', 'from'}
        identifiers = [i for i in identifiers if i.lower() not in keywords]

        if not identifiers:
            return 0.0

        return sum(len(i) for i in identifiers) / len(identifiers)

    def _suggest_refactorings(self, code: str) -> List[str]:
        """Suggest potential refactorings."""
        suggestions = []

        # Check for long functions
        lines = code.split('\n')
        if len(lines) > 30:
            suggestions.append('Consider breaking long function into smaller functions')

        # Check for duplication (simple check)
        line_counts = {}
        for line in lines:
            stripped = line.strip()
            if len(stripped) > 10:  # Ignore very short lines
                line_counts[stripped] = line_counts.get(stripped, 0) + 1

        duplicates = [line for line, count in line_counts.items() if count > 2]
        if duplicates:
            suggestions.append(f'Found {len(duplicates)} duplicated code patterns - consider extraction')

        # Check for magic numbers
        import re
        magic_numbers = re.findall(r'\b\d+\b', code)
        if len(magic_numbers) > 5:
            suggestions.append('Consider extracting magic numbers to named constants')

        # Check for long parameter lists
        if 'def ' in code or 'function' in code:
            param_matches = re.findall(r'\(([^)]+)\)', code)
            for params in param_matches:
                if params.count(',') > 3:
                    suggestions.append('Consider using parameter object for functions with many parameters')
                    break

        if not suggestions:
            suggestions.append('Code looks clean - no obvious refactorings needed')

        return suggestions

    def generate_workflow_summary(self) -> str:
        """Generate summary of TDD workflow progress."""
        summary = [
            "# TDD Workflow Summary\n",
            f"Current Phase: {self.current_phase.value.upper()}",
            f"Current State: {self.state.value.replace('_', ' ').title()}",
            f"Completed Cycles: {len(self.history)}\n"
        ]

        summary.append("## TDD Cycle Steps:\n")
        summary.append("1. **RED**: Write a failing test")
        summary.append("   - Test describes desired behavior")
        summary.append("   - Test fails (no implementation)\n")

        summary.append("2. **GREEN**: Make the test pass")
        summary.append("   - Write minimal code to pass test")
        summary.append("   - All tests should pass\n")

        summary.append("3. **REFACTOR**: Improve the code")
        summary.append("   - Clean up implementation")
        summary.append("   - Tests still pass")
        summary.append("   - Code is more maintainable\n")

        return "\n".join(summary)

    def get_phase_guidance(self, phase: Optional[TDDPhase] = None) -> Dict[str, Any]:
        """
        Get detailed guidance for a specific phase.

        Args:
            phase: TDD phase (uses current if not specified)

        Returns:
            Detailed guidance dictionary
        """
        target_phase = phase or self.current_phase

        if target_phase == TDDPhase.RED:
            return {
                'phase': 'RED',
                'goal': 'Write a failing test',
                'steps': [
                    '1. Read and understand the requirement',
                    '2. Think about expected behavior',
                    '3. Write test that verifies this behavior',
                    '4. Run test and ensure it fails',
                    '5. Verify failure reason is correct (not syntax error)'
                ],
                'common_mistakes': [
                    'Test passes immediately (no real assertion)',
                    'Test fails for wrong reason (syntax error)',
                    'Test is too broad or tests multiple things'
                ],
                'tips': [
                    'Start with simplest test case',
                    'One assertion per test (focused)',
                    'Test should read like specification'
                ]
            }

        elif target_phase == TDDPhase.GREEN:
            return {
                'phase': 'GREEN',
                'goal': 'Make the test pass with minimal code',
                'steps': [
                    '1. Write simplest code that makes test pass',
                    '2. Run test and verify it passes',
                    '3. Run all tests to ensure no regression',
                    '4. Resist urge to add extra features'
                ],
                'common_mistakes': [
                    'Over-engineering solution',
                    'Adding features not covered by tests',
                    'Breaking existing tests'
                ],
                'tips': [
                    'Fake it till you make it (hardcode if needed)',
                    'Triangulate with more tests if needed',
                    'Keep implementation simple'
                ]
            }

        elif target_phase == TDDPhase.REFACTOR:
            return {
                'phase': 'REFACTOR',
                'goal': 'Improve code quality while keeping tests green',
                'steps': [
                    '1. Identify code smells or duplication',
                    '2. Apply one refactoring at a time',
                    '3. Run tests after each change',
                    '4. Commit when satisfied with quality'
                ],
                'common_mistakes': [
                    'Changing behavior (breaking tests)',
                    'Refactoring too much at once',
                    'Skipping this phase'
                ],
                'tips': [
                    'Extract methods for better naming',
                    'Remove duplication',
                    'Improve variable names',
                    'Tests are safety net - use them!'
                ]
            }

        return {}
