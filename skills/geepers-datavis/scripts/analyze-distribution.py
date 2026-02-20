#!/usr/bin/env python3
"""
Data Distribution Analyzer for Scale Selection

Analyzes a data column and recommends appropriate D3 scale type.

Usage:
    python analyze-distribution.py data.csv --column value
    python analyze-distribution.py data.json --column population --format json
    cat data.csv | python analyze-distribution.py --stdin --column amount

Output:
    - Min, max, range
    - Mean, median, standard deviation
    - Skew ratio and distribution shape
    - Recommended scale (linear, log, sqrt, symlog)
    - D3.js code snippet

Author: Luke Steuber
"""

import argparse
import csv
import json
import math
import sys
from typing import List, Dict, Any, Optional


def load_csv(filepath: str, column: str) -> List[float]:
    """Load numeric values from CSV column."""
    values = []
    with open(filepath, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f)
        if column not in reader.fieldnames:
            available = ', '.join(reader.fieldnames or [])
            raise ValueError(f"Column '{column}' not found. Available: {available}")

        for row in reader:
            try:
                val = row[column]
                if val and val.strip():
                    # Handle commas in numbers
                    val = val.replace(',', '').replace('$', '').replace('%', '')
                    values.append(float(val))
            except (ValueError, TypeError):
                continue

    return values


def load_json(filepath: str, column: str) -> List[float]:
    """Load numeric values from JSON array."""
    with open(filepath, 'r', encoding='utf-8') as f:
        data = json.load(f)

    if isinstance(data, list):
        values = []
        for item in data:
            if isinstance(item, dict) and column in item:
                try:
                    values.append(float(item[column]))
                except (ValueError, TypeError):
                    continue
            elif isinstance(item, (int, float)):
                values.append(float(item))
        return values

    raise ValueError("JSON must be an array of objects or numbers")


def load_stdin(column: str) -> List[float]:
    """Load from stdin (CSV format)."""
    values = []
    reader = csv.DictReader(sys.stdin)
    for row in reader:
        try:
            if column in row and row[column]:
                val = row[column].replace(',', '').replace('$', '').replace('%', '')
                values.append(float(val))
        except (ValueError, TypeError):
            continue
    return values


def calculate_statistics(values: List[float]) -> Dict[str, Any]:
    """Calculate distribution statistics."""
    if not values:
        raise ValueError("No valid numeric values found")

    n = len(values)
    sorted_vals = sorted(values)

    # Basic stats
    min_val = min(values)
    max_val = max(values)
    range_val = max_val - min_val

    # Mean
    mean = sum(values) / n

    # Median
    mid = n // 2
    if n % 2 == 0:
        median = (sorted_vals[mid - 1] + sorted_vals[mid]) / 2
    else:
        median = sorted_vals[mid]

    # Standard deviation
    variance = sum((x - mean) ** 2 for x in values) / n
    std_dev = math.sqrt(variance)

    # Percentiles
    def percentile(p):
        k = (n - 1) * p / 100
        f = math.floor(k)
        c = math.ceil(k)
        if f == c:
            return sorted_vals[int(k)]
        return sorted_vals[f] * (c - k) + sorted_vals[c] * (k - f)

    p25 = percentile(25)
    p75 = percentile(75)
    p95 = percentile(95)
    p99 = percentile(99)

    # Skew indicators
    skew_ratio = mean / median if median != 0 else float('inf')

    # Range ratio (orders of magnitude)
    if min_val > 0:
        range_ratio = max_val / min_val
    elif min_val == 0:
        # Find smallest non-zero
        non_zero = [v for v in values if v > 0]
        range_ratio = max_val / min(non_zero) if non_zero else float('inf')
    else:
        range_ratio = float('inf')  # Has negatives

    # Count zeros and negatives
    zeros = sum(1 for v in values if v == 0)
    negatives = sum(1 for v in values if v < 0)

    return {
        'count': n,
        'min': min_val,
        'max': max_val,
        'range': range_val,
        'mean': mean,
        'median': median,
        'std_dev': std_dev,
        'p25': p25,
        'p75': p75,
        'p95': p95,
        'p99': p99,
        'skew_ratio': skew_ratio,
        'range_ratio': range_ratio,
        'zeros': zeros,
        'negatives': negatives,
    }


def recommend_scale(stats: Dict[str, Any]) -> Dict[str, Any]:
    """Recommend D3 scale based on distribution."""
    has_negatives = stats['negatives'] > 0
    has_zeros = stats['zeros'] > 0
    range_ratio = stats['range_ratio']
    skew_ratio = stats['skew_ratio']

    reasons = []
    scale_type = 'linear'
    confidence = 'high'

    # Decision tree
    if has_negatives:
        if range_ratio > 100:
            scale_type = 'symlog'
            reasons.append(f"Data has negatives ({stats['negatives']}) and large range ({range_ratio:.0f}x)")
            reasons.append("Symlog handles zero-crossing with log-like compression")
        else:
            scale_type = 'linear'
            reasons.append(f"Data has negatives but moderate range ({range_ratio:.0f}x)")

    elif range_ratio > 1000:
        scale_type = 'log'
        reasons.append(f"Data spans {range_ratio:.0f}x (>1000x) - log scale required")
        if has_zeros:
            reasons.append(f"Warning: {stats['zeros']} zero values - consider symlog or offset")
            confidence = 'medium'

    elif range_ratio > 100:
        if skew_ratio > 3:
            scale_type = 'log'
            reasons.append(f"Right-skewed (mean/median = {skew_ratio:.1f}) with {range_ratio:.0f}x range")
        else:
            scale_type = 'sqrt'
            reasons.append(f"Moderate range ({range_ratio:.0f}x) - sqrt provides gentle compression")
        if has_zeros:
            reasons.append(f"Note: {stats['zeros']} zero values present")

    elif skew_ratio > 2:
        scale_type = 'sqrt'
        reasons.append(f"Right-skewed distribution (mean/median = {skew_ratio:.1f})")
        reasons.append("Sqrt scale compresses high values while keeping low values readable")

    else:
        scale_type = 'linear'
        reasons.append(f"Data is relatively uniform (range {range_ratio:.0f}x, skew {skew_ratio:.2f})")

    return {
        'recommended_scale': scale_type,
        'confidence': confidence,
        'reasons': reasons,
    }


def generate_d3_code(stats: Dict, recommendation: Dict, domain_name: str = 'data') -> str:
    """Generate D3.js scale code snippet."""
    scale = recommendation['recommended_scale']
    min_val = stats['min']
    max_val = stats['max']

    # Round domain for cleaner code
    def nice_round(val, direction='up'):
        if val == 0:
            return 0
        magnitude = 10 ** math.floor(math.log10(abs(val)))
        if direction == 'up':
            return math.ceil(val / magnitude) * magnitude
        else:
            return math.floor(val / magnitude) * magnitude

    if scale == 'linear':
        domain_min = nice_round(min_val, 'down') if min_val > 0 else min_val
        domain_max = nice_round(max_val, 'up')
        return f"""const scale = d3.scaleLinear()
  .domain([{domain_min}, {domain_max}])
  .range([0, width])
  .nice();"""

    elif scale == 'log':
        domain_min = max(1, nice_round(min_val, 'down')) if min_val > 0 else 1
        domain_max = nice_round(max_val, 'up')
        return f"""const scale = d3.scaleLog()
  .domain([{domain_min}, {domain_max}])
  .range([0, width])
  .clamp(true);

// Note: Log scale requires positive domain (min > 0)
// For zero values, consider offset: d => d + 1"""

    elif scale == 'sqrt':
        domain_max = nice_round(max_val, 'up')
        return f"""const scale = d3.scaleSqrt()
  .domain([0, {domain_max}])
  .range([0, maxRadius]);

// Sqrt scale is ideal for area encoding (circles, bubbles)
// Ensures perceptually accurate size perception"""

    elif scale == 'symlog':
        domain_min = nice_round(min_val, 'down')
        domain_max = nice_round(max_val, 'up')
        return f"""const scale = d3.scaleSymlog()
  .domain([{domain_min}, {domain_max}])
  .range([0, width])
  .constant(1);  // Adjust for transition smoothness around zero

// Symlog handles negative values and zero crossing gracefully"""

    return "// Unable to generate scale code"


def format_number(val: float) -> str:
    """Format number for display."""
    if abs(val) >= 1_000_000_000:
        return f"{val/1_000_000_000:.2f}B"
    elif abs(val) >= 1_000_000:
        return f"{val/1_000_000:.2f}M"
    elif abs(val) >= 1_000:
        return f"{val/1_000:.2f}K"
    elif abs(val) < 0.01 and val != 0:
        return f"{val:.2e}"
    else:
        return f"{val:.2f}"


def print_report(stats: Dict, recommendation: Dict, column: str, output_format: str):
    """Print analysis report."""
    if output_format == 'json':
        output = {
            'column': column,
            'statistics': stats,
            'recommendation': recommendation,
        }
        print(json.dumps(output, indent=2, default=str))
        return

    # Text report
    print("\n" + "=" * 60)
    print(f"  DISTRIBUTION ANALYSIS: {column}")
    print("=" * 60)

    print("\n  STATISTICS")
    print("  " + "-" * 40)
    print(f"  Count:      {stats['count']:,}")
    print(f"  Min:        {format_number(stats['min'])}")
    print(f"  Max:        {format_number(stats['max'])}")
    print(f"  Range:      {format_number(stats['range'])}")
    print(f"  Mean:       {format_number(stats['mean'])}")
    print(f"  Median:     {format_number(stats['median'])}")
    print(f"  Std Dev:    {format_number(stats['std_dev'])}")

    print("\n  PERCENTILES")
    print("  " + "-" * 40)
    print(f"  25th:       {format_number(stats['p25'])}")
    print(f"  75th:       {format_number(stats['p75'])}")
    print(f"  95th:       {format_number(stats['p95'])}")
    print(f"  99th:       {format_number(stats['p99'])}")

    print("\n  DISTRIBUTION SHAPE")
    print("  " + "-" * 40)
    print(f"  Skew Ratio: {stats['skew_ratio']:.2f} (mean/median)")
    print(f"  Range Ratio: {stats['range_ratio']:.0f}x (max/min)")
    print(f"  Zeros:      {stats['zeros']}")
    print(f"  Negatives:  {stats['negatives']}")

    print("\n  RECOMMENDATION")
    print("  " + "-" * 40)
    print(f"  Scale:      {recommendation['recommended_scale'].upper()}")
    print(f"  Confidence: {recommendation['confidence']}")
    print("\n  Reasons:")
    for reason in recommendation['reasons']:
        print(f"    - {reason}")

    print("\n  D3.JS CODE")
    print("  " + "-" * 40)
    code = generate_d3_code(stats, recommendation, column)
    for line in code.split('\n'):
        print(f"  {line}")

    print("\n" + "=" * 60 + "\n")


def main():
    parser = argparse.ArgumentParser(
        description='Analyze data distribution and recommend D3 scale',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s data.csv --column population
  %(prog)s data.json --column value --format json
  cat data.csv | %(prog)s --stdin --column amount
        """
    )

    parser.add_argument('file', nargs='?',
                        help='Input file (CSV or JSON)')
    parser.add_argument('--column', '-c', required=True,
                        help='Column name to analyze')
    parser.add_argument('--stdin', action='store_true',
                        help='Read from stdin (CSV format)')
    parser.add_argument('--format', '-f',
                        choices=['text', 'json'],
                        default='text',
                        help='Output format (default: text)')

    args = parser.parse_args()

    # Load data
    try:
        if args.stdin:
            values = load_stdin(args.column)
        elif args.file:
            if args.file.endswith('.json'):
                values = load_json(args.file, args.column)
            else:
                values = load_csv(args.file, args.column)
        else:
            parser.error("Must specify file or --stdin")

        if not values:
            print(f"Error: No valid numeric values found in column '{args.column}'",
                  file=sys.stderr)
            sys.exit(1)

        # Analyze
        stats = calculate_statistics(values)
        recommendation = recommend_scale(stats)

        # Output
        print_report(stats, recommendation, args.column, args.format)

    except FileNotFoundError:
        print(f"Error: File '{args.file}' not found", file=sys.stderr)
        sys.exit(1)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
