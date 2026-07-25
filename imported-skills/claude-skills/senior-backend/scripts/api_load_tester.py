#!/usr/bin/env python3
"""
API Load Tester

Performs HTTP load testing with configurable concurrency, measuring latency
percentiles, throughput, and error rates.

Usage:
    python api_load_tester.py https://api.example.com/users --concurrency 50 --duration 30
    python api_load_tester.py https://api.example.com/orders --method POST --body '{"item": 1}'
    python api_load_tester.py https://api.example.com/v1/users https://api.example.com/v2/users --compare
"""

import os
import sys
import json
import argparse
import time
import statistics
import threading
import queue
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict
from typing import Dict, List, Optional, Tuple
from datetime import datetime
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError
from urllib.parse import urlparse
import ssl


@dataclass
class RequestResult:
    """Result of a single HTTP request."""
    success: bool
    status_code: int
    latency_ms: float
    error: Optional[str] = None
    response_size: int = 0


@dataclass
class LoadTestResults:
    """Aggregated load test results."""
    target_url: str
    method: str
    duration_seconds: float
    concurrency: int
    total_requests: int
    successful_requests: int
    failed_requests: int
    requests_per_second: float

    # Latency metrics (milliseconds)
    latency_min: float
    latency_max: float
    latency_avg: float
    latency_p50: float
    latency_p90: float
    latency_p95: float
    latency_p99: float
    latency_stddev: float

    # Error breakdown
    errors_by_type: Dict[str, int] = field(default_factory=dict)

    # Transfer metrics
    total_bytes_received: int = 0
    throughput_mbps: float = 0.0

    def success_rate(self) -> float:
        """Calculate success rate percentage."""
        if self.total_requests == 0:
            return 0.0
        return (self.successful_requests / self.total_requests) * 100


def calculate_percentile(data: List[float], percentile: float) -> float:
    """Calculate percentile from sorted data."""
    if not data:
        return 0.0
    k = (len(data) - 1) * (percentile / 100)
    f = int(k)
    c = f + 1 if f + 1 < len(data) else f
    return data[f] + (data[c] - data[f]) * (k - f)


class HTTPClient:
    """HTTP client with configurable settings."""

    def __init__(self, timeout: float = 30.0, headers: Optional[Dict[str, str]] = None,
                 verify_ssl: bool = True):
        self.timeout = timeout
        self.headers = headers or {}
        self.verify_ssl = verify_ssl

        # Create SSL context
        if not verify_ssl:
            self.ssl_context = ssl.create_default_context()
            self.ssl_context.check_hostname = False
            self.ssl_context.verify_mode = ssl.CERT_NONE
        else:
            self.ssl_context = None

    def request(self, url: str, method: str = 'GET', body: Optional[bytes] = None) -> RequestResult:
        """Execute HTTP request and return result."""
        start_time = time.perf_counter()

        try:
            request = Request(url, data=body, method=method)

            # Add headers
            for key, value in self.headers.items():
                request.add_header(key, value)

            # Add content-type for POST/PUT
            if body and method in ['POST', 'PUT', 'PATCH']:
                if 'Content-Type' not in self.headers:
                    request.add_header('Content-Type', 'application/json')

            # Execute request
            with urlopen(request, timeout=self.timeout, context=self.ssl_context) as response:
                response_data = response.read()
                elapsed = (time.perf_counter() - start_time) * 1000

                return RequestResult(
                    success=True,
                    status_code=response.status,
                    latency_ms=elapsed,
                    response_size=len(response_data),
                )

        except HTTPError as e:
            elapsed = (time.perf_counter() - start_time) * 1000
            return RequestResult(
                success=False,
                status_code=e.code,
                latency_ms=elapsed,
                error=f"HTTP {e.code}: {e.reason}",
            )

        except URLError as e:
            elapsed = (time.perf_counter() - start_time) * 1000
            return RequestResult(
                success=False,
                status_code=0,
                latency_ms=elapsed,
                error=f"Connection error: {str(e.reason)}",
            )

        except TimeoutError:
            elapsed = (time.perf_counter() - start_time) * 1000
            return RequestResult(
                success=False,
                status_code=0,
                latency_ms=elapsed,
                error="Connection timeout",
            )

        except Exception as e:
            elapsed = (time.perf_counter() - start_time) * 1000
            return RequestResult(
                success=False,
                status_code=0,
                latency_ms=elapsed,
                error=str(e),
            )


class LoadTester:
    """HTTP load testing engine."""

    def __init__(self, url: str, method: str = 'GET', body: Optional[str] = None,
                 headers: Optional[Dict[str, str]] = None, concurrency: int = 10,
                 duration: float = 10.0, timeout: float = 30.0, verify_ssl: bool = True):
        self.url = url
        self.method = method.upper()
        self.body = body.encode() if body else None
        self.headers = headers or {}
        self.concurrency = concurrency
        self.duration = duration
        self.timeout = timeout
        self.verify_ssl = verify_ssl

        self.results: List[RequestResult] = []
        self.stop_event = threading.Event()
        self.results_lock = threading.Lock()

    def run(self) -> LoadTestResults:
        """Execute load test and return results."""
        print(f"Load Testing: {self.url}")
        print(f"Method: {self.method}")
        print(f"Concurrency: {self.concurrency}")
        print(f"Duration: {self.duration}s")
        print("-" * 50)

        self.results = []
        self.stop_event.clear()

        start_time = time.time()

        # Start worker threads
        with ThreadPoolExecutor(max_workers=self.concurrency) as executor:
            futures = []
            for _ in range(self.concurrency):
                future = executor.submit(self._worker)
                futures.append(future)

            # Wait for duration
            time.sleep(self.duration)
            self.stop_event.set()

            # Wait for workers to finish
            for future in as_completed(futures):
                try:
                    future.result()
                except Exception as e:
                    print(f"Worker error: {e}")

        elapsed_time = time.time() - start_time

        return self._aggregate_results(elapsed_time)

    def _worker(self):
        """Worker thread that continuously sends requests."""
        client = HTTPClient(
            timeout=self.timeout,
            headers=self.headers,
            verify_ssl=self.verify_ssl,
        )

        while not self.stop_event.is_set():
            result = client.request(self.url, self.method, self.body)

            with self.results_lock:
                self.results.append(result)

    def _aggregate_results(self, elapsed_time: float) -> LoadTestResults:
        """Aggregate individual results into summary."""
        if not self.results:
            return LoadTestResults(
                target_url=self.url,
                method=self.method,
                duration_seconds=elapsed_time,
                concurrency=self.concurrency,
                total_requests=0,
                successful_requests=0,
                failed_requests=0,
                requests_per_second=0,
                latency_min=0,
                latency_max=0,
                latency_avg=0,
                latency_p50=0,
                latency_p90=0,
                latency_p95=0,
                latency_p99=0,
                latency_stddev=0,
            )

        # Separate successful and failed
        successful = [r for r in self.results if r.success]
        failed = [r for r in self.results if not r.success]

        # Latency calculations (from successful requests)
        latencies = sorted([r.latency_ms for r in successful]) if successful else [0]

        # Error breakdown
        errors_by_type: Dict[str, int] = {}
        for r in failed:
            error_type = r.error or 'Unknown'
            errors_by_type[error_type] = errors_by_type.get(error_type, 0) + 1

        # Calculate throughput
        total_bytes = sum(r.response_size for r in successful)
        throughput_mbps = (total_bytes * 8) / (elapsed_time * 1_000_000) if elapsed_time > 0 else 0

        return LoadTestResults(
            target_url=self.url,
            method=self.method,
            duration_seconds=elapsed_time,
            concurrency=self.concurrency,
            total_requests=len(self.results),
            successful_requests=len(successful),
            failed_requests=len(failed),
            requests_per_second=len(self.results) / elapsed_time if elapsed_time > 0 else 0,
            latency_min=min(latencies),
            latency_max=max(latencies),
            latency_avg=statistics.mean(latencies) if latencies else 0,
            latency_p50=calculate_percentile(latencies, 50),
            latency_p90=calculate_percentile(latencies, 90),
            latency_p95=calculate_percentile(latencies, 95),
            latency_p99=calculate_percentile(latencies, 99),
            latency_stddev=statistics.stdev(latencies) if len(latencies) > 1 else 0,
            errors_by_type=errors_by_type,
            total_bytes_received=total_bytes,
            throughput_mbps=throughput_mbps,
        )


def print_results(results: LoadTestResults, verbose: bool = False):
    """Print formatted load test results."""
    print("\n" + "=" * 60)
    print("LOAD TEST RESULTS")
    print("=" * 60)

    print(f"\nTarget: {results.target_url}")
    print(f"Method: {results.method}")
    print(f"Duration: {results.duration_seconds:.1f}s")
    print(f"Concurrency: {results.concurrency}")

    print(f"\nTHROUGHPUT:")
    print(f"  Total requests: {results.total_requests:,}")
    print(f"  Requests/sec: {results.requests_per_second:.1f}")
    print(f"  Successful: {results.successful_requests:,} ({results.success_rate():.1f}%)")
    print(f"  Failed: {results.failed_requests:,}")

    print(f"\nLATENCY (ms):")
    print(f"  Min: {results.latency_min:.1f}")
    print(f"  Avg: {results.latency_avg:.1f}")
    print(f"  P50: {results.latency_p50:.1f}")
    print(f"  P90: {results.latency_p90:.1f}")
    print(f"  P95: {results.latency_p95:.1f}")
    print(f"  P99: {results.latency_p99:.1f}")
    print(f"  Max: {results.latency_max:.1f}")
    print(f"  StdDev: {results.latency_stddev:.1f}")

    if results.errors_by_type:
        print(f"\nERRORS:")
        for error_type, count in sorted(results.errors_by_type.items(), key=lambda x: -x[1]):
            print(f"  {error_type}: {count}")

    if verbose:
        print(f"\nTRANSFER:")
        print(f"  Total bytes: {results.total_bytes_received:,}")
        print(f"  Throughput: {results.throughput_mbps:.2f} Mbps")

    # Recommendations
    print(f"\nRECOMMENDATIONS:")

    if results.latency_p99 > 500:
        print(f"  Warning: P99 latency ({results.latency_p99:.0f}ms) exceeds 500ms")
        print(f"    Consider: Connection pooling, query optimization, caching")

    if results.latency_p95 > 200:
        print(f"  Warning: P95 latency ({results.latency_p95:.0f}ms) exceeds 200ms target")

    if results.success_rate() < 99.0:
        print(f"  Warning: Success rate ({results.success_rate():.1f}%) below 99%")
        print(f"    Check server capacity and error logs")

    if results.latency_stddev > results.latency_avg:
        print(f"  Warning: High latency variance (stddev > avg)")
        print(f"    Indicates inconsistent performance")

    if results.success_rate() >= 99.0 and results.latency_p95 <= 200:
        print(f"  Performance looks good for this load level")

    print("=" * 60)


def compare_results(results1: LoadTestResults, results2: LoadTestResults):
    """Compare two load test results."""
    print("\n" + "=" * 60)
    print("COMPARISON RESULTS")
    print("=" * 60)

    print(f"\n{'Metric':<25} {'Endpoint 1':<15} {'Endpoint 2':<15} {'Diff':<15}")
    print("-" * 70)

    # Helper to format diff
    def diff_str(v1: float, v2: float, lower_better: bool = True) -> str:
        if v1 == 0:
            return "N/A"
        diff_pct = ((v2 - v1) / v1) * 100
        symbol = "-" if (diff_pct < 0) == lower_better else "+"
        color_good = diff_pct < 0 if lower_better else diff_pct > 0
        return f"{symbol}{abs(diff_pct):.1f}%"

    metrics = [
        ("Requests/sec", results1.requests_per_second, results2.requests_per_second, False),
        ("Success rate (%)", results1.success_rate(), results2.success_rate(), False),
        ("Latency Avg (ms)", results1.latency_avg, results2.latency_avg, True),
        ("Latency P50 (ms)", results1.latency_p50, results2.latency_p50, True),
        ("Latency P90 (ms)", results1.latency_p90, results2.latency_p90, True),
        ("Latency P95 (ms)", results1.latency_p95, results2.latency_p95, True),
        ("Latency P99 (ms)", results1.latency_p99, results2.latency_p99, True),
    ]

    for name, v1, v2, lower_better in metrics:
        print(f"{name:<25} {v1:<15.1f} {v2:<15.1f} {diff_str(v1, v2, lower_better):<15}")

    print("-" * 70)

    # Summary
    print(f"\nEndpoint 1: {results1.target_url}")
    print(f"Endpoint 2: {results2.target_url}")

    # Determine winner
    score1, score2 = 0, 0

    if results1.requests_per_second > results2.requests_per_second:
        score1 += 1
    else:
        score2 += 1

    if results1.latency_p95 < results2.latency_p95:
        score1 += 1
    else:
        score2 += 1

    if results1.success_rate() > results2.success_rate():
        score1 += 1
    else:
        score2 += 1

    print(f"\nOverall: {'Endpoint 1' if score1 > score2 else 'Endpoint 2'} performs better")

    print("=" * 60)


class APILoadTester:
    """Main load tester class with CLI integration."""

    def __init__(self, urls: List[str], method: str = 'GET', body: Optional[str] = None,
                 headers: Optional[Dict[str, str]] = None, concurrency: int = 10,
                 duration: float = 10.0, timeout: float = 30.0, compare: bool = False,
                 verbose: bool = False, verify_ssl: bool = True):
        self.urls = urls
        self.method = method
        self.body = body
        self.headers = headers or {}
        self.concurrency = concurrency
        self.duration = duration
        self.timeout = timeout
        self.compare = compare
        self.verbose = verbose
        self.verify_ssl = verify_ssl

    def run(self) -> Dict:
        """Execute load test(s) and return results."""
        results = []

        for url in self.urls:
            tester = LoadTester(
                url=url,
                method=self.method,
                body=self.body,
                headers=self.headers,
                concurrency=self.concurrency,
                duration=self.duration,
                timeout=self.timeout,
                verify_ssl=self.verify_ssl,
            )

            result = tester.run()
            results.append(result)

            if not self.compare:
                print_results(result, self.verbose)

        if self.compare and len(results) >= 2:
            compare_results(results[0], results[1])

        return {
            'status': 'success',
            'results': [asdict(r) for r in results],
        }


def parse_headers(header_args: Optional[List[str]]) -> Dict[str, str]:
    """Parse header arguments into dictionary."""
    headers = {}
    if header_args:
        for h in header_args:
            if ':' in h:
                key, value = h.split(':', 1)
                headers[key.strip()] = value.strip()
    return headers


def main():
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description='HTTP load testing tool',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  %(prog)s https://api.example.com/users --concurrency 50 --duration 30
  %(prog)s https://api.example.com/orders --method POST --body '{"item": 1}'
  %(prog)s https://api.example.com/v1 https://api.example.com/v2 --compare
  %(prog)s https://api.example.com/health --header "Authorization: Bearer token"
        '''
    )

    parser.add_argument(
        'urls',
        nargs='+',
        help='URL(s) to test'
    )
    parser.add_argument(
        '--method', '-m',
        default='GET',
        choices=['GET', 'POST', 'PUT', 'PATCH', 'DELETE'],
        help='HTTP method (default: GET)'
    )
    parser.add_argument(
        '--body', '-b',
        help='Request body (JSON string)'
    )
    parser.add_argument(
        '--header', '-H',
        action='append',
        dest='headers',
        help='HTTP header (format: "Name: Value")'
    )
    parser.add_argument(
        '--concurrency', '-c',
        type=int,
        default=10,
        help='Number of concurrent requests (default: 10)'
    )
    parser.add_argument(
        '--duration', '-d',
        type=float,
        default=10.0,
        help='Test duration in seconds (default: 10)'
    )
    parser.add_argument(
        '--timeout', '-t',
        type=float,
        default=30.0,
        help='Request timeout in seconds (default: 30)'
    )
    parser.add_argument(
        '--compare',
        action='store_true',
        help='Compare two endpoints (requires two URLs)'
    )
    parser.add_argument(
        '--no-verify-ssl',
        action='store_true',
        help='Disable SSL certificate verification'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Enable verbose output'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )
    parser.add_argument(
        '--output', '-o',
        help='Output file path for results'
    )

    args = parser.parse_args()

    # Validate
    if args.compare and len(args.urls) < 2:
        print("Error: --compare requires two URLs", file=sys.stderr)
        sys.exit(1)

    # Parse headers
    headers = parse_headers(args.headers)

    try:
        tester = APILoadTester(
            urls=args.urls,
            method=args.method,
            body=args.body,
            headers=headers,
            concurrency=args.concurrency,
            duration=args.duration,
            timeout=args.timeout,
            compare=args.compare,
            verbose=args.verbose,
            verify_ssl=not args.no_verify_ssl,
        )

        results = tester.run()

        if args.json:
            output = json.dumps(results, indent=2)
            if args.output:
                with open(args.output, 'w') as f:
                    f.write(output)
                print(f"\nResults written to: {args.output}")
            else:
                print(output)
        elif args.output:
            with open(args.output, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"\nResults written to: {args.output}")

    except KeyboardInterrupt:
        print("\nTest interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
