#!/usr/bin/env python3
"""Skills 2.0 Eval Runner — Automated quality verification for skills.

Loads eval definitions from eval.yaml, runs each eval case, and produces
a structured report with pass rates, execution times, and comparison data.

Usage:
    python eval_runner.py [--eval-dir DIR] [--eval-name NAME] [--json] [--verbose]

Exit codes:
    0 — All evals passed
    1 — One or more evals failed
    2 — Configuration error
"""

__version__ = '1.0.0'

import argparse
import json
import os
import sys
import time

import yaml  # type: ignore[import-untyped]


def load_eval_config(eval_dir):
    """Load and validate eval.yaml from the given directory.

    Returns:
        dict: Parsed eval configuration.

    Raises:
        SystemExit: If eval.yaml is missing or malformed.
    """
    config_path = os.path.join(eval_dir, 'eval.yaml')
    if not os.path.isfile(config_path):
        print(f'Error: eval.yaml not found at {config_path}', file=sys.stderr)
        sys.exit(2)

    try:
        with open(config_path, 'r') as fh:
            config = yaml.safe_load(fh)
    except yaml.YAMLError as e:
        print(f'Error: failed to parse eval.yaml: {e}', file=sys.stderr)
        sys.exit(2)

    if not isinstance(config, dict):
        print('Error: eval.yaml must be a YAML mapping', file=sys.stderr)
        sys.exit(2)

    if 'evals' not in config:
        print('Error: eval.yaml must contain an "evals" key', file=sys.stderr)
        sys.exit(2)

    if not isinstance(config['evals'], list):
        print('Error: "evals" must be a list', file=sys.stderr)
        sys.exit(2)

    return config


def validate_eval_entry(entry, eval_dir):
    """Validate a single eval entry has all required fields and files exist.

    Returns:
        list[str]: List of validation error messages (empty = valid).
    """
    errors = []
    required_fields = ['name', 'prompt', 'expected', 'criteria']
    for field in required_fields:
        if field not in entry:
            errors.append(f'Missing required field: {field}')

    if 'prompt' in entry:
        prompt_path = os.path.join(eval_dir, entry['prompt'])
        if not os.path.isfile(prompt_path):
            errors.append(f'Prompt file not found: {prompt_path}')

    if 'expected' in entry:
        expected_path = os.path.join(eval_dir, entry['expected'])
        if not os.path.isfile(expected_path):
            errors.append(f'Expected file not found: {expected_path}')

    if 'criteria' in entry:
        if not isinstance(entry['criteria'], list):
            errors.append('"criteria" must be a list')
        else:
            for i, criterion in enumerate(entry['criteria']):
                if isinstance(criterion, dict):
                    if 'description' not in criterion:
                        errors.append(
                            f'Criterion {i} missing "description"')
                elif not isinstance(criterion, str):
                    errors.append(
                        f'Criterion {i} must be a string or dict')

    if 'timeout' in entry:
        if not isinstance(entry['timeout'], (int, float)):
            errors.append('"timeout" must be a number')
        elif entry['timeout'] <= 0:
            errors.append('"timeout" must be positive')

    return errors


def load_file_content(filepath):
    """Load content from a file, returning empty string on error."""
    try:
        with open(filepath, 'r') as fh:
            return fh.read()
    except OSError:
        return ''


def extract_criteria_text(criteria):
    """Extract text descriptions from criteria list (supports str and dict)."""
    texts = []
    for c in criteria:
        if isinstance(c, str):
            texts.append(c)
        elif isinstance(c, dict):
            texts.append(c.get('description', str(c)))
    return texts


def evaluate_criteria(expected_content, criteria_texts):
    """Evaluate criteria against expected content.

    This is a structural validation — it checks that the expected file
    contains content that addresses each criterion.

    Returns:
        list[dict]: Results for each criterion with pass/fail and details.
    """
    results = []
    for criterion_text in criteria_texts:
        # Extract key terms from the criterion for matching
        key_terms = []
        words = criterion_text.lower().split()
        # Filter out common words to find meaningful terms
        stop_words = {
            'must', 'should', 'the', 'a', 'an', 'is', 'are', 'for',
            'and', 'or', 'of', 'in', 'to', 'with', 'that', 'this',
            'be', 'have', 'has', 'not', 'from', 'at', 'by', 'on',
        }
        for word in words:
            cleaned = word.strip('"\'.,;:!?()[]{}')
            if cleaned and cleaned not in stop_words and len(cleaned) > 2:
                key_terms.append(cleaned)

        # Check if expected content addresses the criterion
        expected_lower = expected_content.lower()
        matched_terms = [t for t in key_terms if t in expected_lower]
        coverage = len(matched_terms) / max(len(key_terms), 1)

        results.append({
            'criterion': criterion_text,
            'passed': coverage >= 0.3,
            'coverage': round(coverage, 2),
            'matched_terms': matched_terms,
            'total_terms': len(key_terms),
        })

    return results


def run_eval(entry, eval_dir, verbose=False):
    """Run a single eval and return results.

    Returns:
        dict: Eval results including pass/fail, timing, and criteria breakdown.
    """
    start_time = time.monotonic()

    # Validate entry
    validation_errors = validate_eval_entry(entry, eval_dir)
    if validation_errors:
        elapsed = (time.monotonic() - start_time) * 1000
        return {
            'name': entry.get('name', '<unknown>'),
            'status': 'error',
            'errors': validation_errors,
            'execution_time_ms': round(elapsed, 1),
            'criteria_results': [],
            'pass_rate': 0.0,
        }

    # Load prompt and expected content
    prompt_path = os.path.join(eval_dir, entry['prompt'])
    expected_path = os.path.join(eval_dir, entry['expected'])

    prompt_content = load_file_content(prompt_path)
    expected_content = load_file_content(expected_path)

    if not prompt_content:
        elapsed = (time.monotonic() - start_time) * 1000
        return {
            'name': entry['name'],
            'status': 'error',
            'errors': [f'Empty prompt file: {prompt_path}'],
            'execution_time_ms': round(elapsed, 1),
            'criteria_results': [],
            'pass_rate': 0.0,
        }

    if not expected_content:
        elapsed = (time.monotonic() - start_time) * 1000
        return {
            'name': entry['name'],
            'status': 'error',
            'errors': [f'Empty expected file: {expected_path}'],
            'execution_time_ms': round(elapsed, 1),
            'criteria_results': [],
            'pass_rate': 0.0,
        }

    # Extract and evaluate criteria
    criteria_texts = extract_criteria_text(entry['criteria'])
    criteria_results = evaluate_criteria(expected_content, criteria_texts)

    passed_count = sum(1 for r in criteria_results if r['passed'])
    total_count = len(criteria_results)
    pass_rate = (passed_count / total_count * 100) if total_count > 0 else 0.0

    elapsed = (time.monotonic() - start_time) * 1000

    # Estimate token count (rough: ~4 chars per token)
    token_estimate = (len(prompt_content) + len(expected_content)) // 4

    status = 'pass' if pass_rate >= 80.0 else 'fail'

    result = {
        'name': entry['name'],
        'status': status,
        'pass_rate': round(pass_rate, 1),
        'passed_criteria': passed_count,
        'total_criteria': total_count,
        'execution_time_ms': round(elapsed, 1),
        'token_estimate': token_estimate,
        'criteria_results': criteria_results,
        'tags': entry.get('tags', []),
    }

    if verbose:
        result['prompt_path'] = prompt_path
        result['expected_path'] = expected_path
        result['prompt_length'] = len(prompt_content)
        result['expected_length'] = len(expected_content)

    return result


def run_all_evals(config, eval_dir, eval_name=None, verbose=False):
    """Run all evals (or a specific one) and return aggregate results.

    Returns:
        dict: Aggregate results including per-eval and summary data.
    """
    evals = config['evals']
    if eval_name:
        evals = [e for e in evals if e.get('name') == eval_name]
        if not evals:
            print(f'Error: eval "{eval_name}" not found', file=sys.stderr)
            sys.exit(2)

    results = []
    for entry in evals:
        result = run_eval(entry, eval_dir, verbose=verbose)
        results.append(result)

    total_evals = len(results)
    passed_evals = sum(1 for r in results if r['status'] == 'pass')
    failed_evals = sum(1 for r in results if r['status'] == 'fail')
    error_evals = sum(1 for r in results if r['status'] == 'error')
    avg_pass_rate = (
        sum(r['pass_rate'] for r in results) / total_evals
        if total_evals > 0 else 0.0
    )
    total_time = sum(r['execution_time_ms'] for r in results)

    return {
        'skill': config.get('skill', '<unknown>'),
        'version': config.get('version', '<unknown>'),
        'classification': config.get('classification', '<unknown>'),
        'deprecation_risk': config.get('deprecation-risk', '<unknown>'),
        'summary': {
            'total_evals': total_evals,
            'passed': passed_evals,
            'failed': failed_evals,
            'errors': error_evals,
            'average_pass_rate': round(avg_pass_rate, 1),
            'total_execution_time_ms': round(total_time, 1),
            'overall_status': 'pass' if failed_evals == 0 and error_evals == 0 else 'fail',
        },
        'evals': results,
        'parity_test': config.get('parity_test', None),
    }


def print_report(report):
    """Print a human-readable eval report."""
    print('=' * 70)
    print(f'  Skills 2.0 Eval Report: {report["skill"]} v{report["version"]}')
    print(f'  Classification: {report["classification"]}  |  '
          f'Deprecation Risk: {report["deprecation_risk"]}')
    print('=' * 70)
    print()

    summary = report['summary']
    status_icon = 'PASS' if summary['overall_status'] == 'pass' else 'FAIL'
    print(f'  Overall: [{status_icon}]  '
          f'{summary["passed"]}/{summary["total_evals"]} passed  '
          f'({summary["average_pass_rate"]}% avg)  '
          f'{summary["total_execution_time_ms"]:.0f}ms total')
    print()

    for ev in report['evals']:
        icon = 'PASS' if ev['status'] == 'pass' else (
            'FAIL' if ev['status'] == 'fail' else 'ERR ')
        print(f'  [{icon}] {ev["name"]}')
        print(f'         Pass rate: {ev["pass_rate"]}%  '
              f'({ev.get("passed_criteria", 0)}/{ev.get("total_criteria", 0)} criteria)  '
              f'{ev["execution_time_ms"]:.1f}ms')

        if ev.get('errors'):
            for err in ev['errors']:
                print(f'         ERROR: {err}')

        if ev.get('criteria_results'):
            for cr in ev['criteria_results']:
                cr_icon = '+' if cr['passed'] else '-'
                print(f'         [{cr_icon}] {cr["criterion"][:60]}...'
                      if len(cr['criterion']) > 60
                      else f'         [{cr_icon}] {cr["criterion"]}')
        print()

    if report.get('parity_test') and report['parity_test'].get('enabled'):
        pt = report['parity_test']
        print('-' * 70)
        print(f'  Parity Test: enabled (threshold: {pt["threshold"]}%)')
        print(f'  Consecutive failures for deprecation: '
              f'{pt["consecutive_failures_for_deprecation"]}')
        print()

    print('=' * 70)


def main():
    parser = argparse.ArgumentParser(
        description='Skills 2.0 Eval Runner — Automated quality verification')
    parser.add_argument(
        '--eval-dir', default=None,
        help='Directory containing eval.yaml (default: evals/ relative to skill root)')
    parser.add_argument(
        '--eval-name', default=None,
        help='Run a specific eval by name')
    parser.add_argument(
        '--json', action='store_true', dest='json_output',
        help='Output results as JSON')
    parser.add_argument(
        '--verbose', action='store_true',
        help='Include additional details in output')
    parser.add_argument(
        '--version', action='version',
        version=f'%(prog)s {__version__}')

    args = parser.parse_args()

    # Determine eval directory
    if args.eval_dir:
        eval_dir = args.eval_dir
    else:
        skill_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        eval_dir = os.path.join(skill_root, 'evals')

    config = load_eval_config(eval_dir)
    report = run_all_evals(config, eval_dir,
                           eval_name=args.eval_name,
                           verbose=args.verbose)

    if args.json_output:
        print(json.dumps(report, indent=2))
    else:
        print_report(report)

    status = report['summary']['overall_status']
    sys.exit(0 if status == 'pass' else 1)


if __name__ == '__main__':
    main()
