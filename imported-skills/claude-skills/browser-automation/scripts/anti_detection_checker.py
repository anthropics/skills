#!/usr/bin/env python3
"""
Anti-Detection Checker - Audits Playwright scripts for common bot detection vectors.

Analyzes a Playwright automation script and identifies patterns that make the
browser detectable as a bot. Produces a risk score (0-100) with specific
recommendations for each issue found.

Detection vectors checked:
- Headless mode usage
- Default/missing user agent configuration
- Viewport size (default 800x600 is a red flag)
- WebDriver flag (navigator.webdriver)
- Navigator property overrides
- Request throttling / human-like delays
- Cookie/session management
- Proxy configuration
- Error handling patterns

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, asdict
from typing import List, Optional


@dataclass
class Finding:
    """A single detection risk finding."""
    category: str
    severity: str  # "critical", "high", "medium", "low", "info"
    description: str
    line: Optional[int]
    recommendation: str
    weight: int  # Points added to risk score (0-15)


SEVERITY_WEIGHTS = {
    "critical": 15,
    "high": 10,
    "medium": 5,
    "low": 2,
    "info": 0,
}


class AntiDetectionChecker:
    """Analyzes Playwright scripts for bot detection vulnerabilities."""

    def __init__(self, script_content: str, file_path: str = "<stdin>"):
        self.content = script_content
        self.lines = script_content.split("\n")
        self.file_path = file_path
        self.findings: List[Finding] = []

    def check_all(self) -> List[Finding]:
        """Run all detection checks."""
        self._check_headless_mode()
        self._check_user_agent()
        self._check_viewport()
        self._check_webdriver_flag()
        self._check_navigator_properties()
        self._check_request_delays()
        self._check_error_handling()
        self._check_proxy()
        self._check_session_management()
        self._check_browser_close()
        self._check_stealth_imports()
        return self.findings

    def _find_line(self, pattern: str) -> Optional[int]:
        """Find the first line number matching a regex pattern."""
        for i, line in enumerate(self.lines, 1):
            if re.search(pattern, line):
                return i
        return None

    def _has_pattern(self, pattern: str) -> bool:
        """Check if pattern exists anywhere in the script."""
        return bool(re.search(pattern, self.content))

    def _check_headless_mode(self):
        """Check if headless mode is properly configured."""
        if self._has_pattern(r"headless\s*=\s*False"):
            self.findings.append(Finding(
                category="Headless Mode",
                severity="high",
                description="Browser launched in headed mode (headless=False). This is fine for development but should be headless=True in production.",
                line=self._find_line(r"headless\s*=\s*False"),
                recommendation="Use headless=True for production. Toggle via environment variable: headless=os.environ.get('HEADLESS', 'true') == 'true'",
                weight=SEVERITY_WEIGHTS["high"],
            ))
        elif not self._has_pattern(r"headless"):
            # Default is headless=True in Playwright, which is correct
            self.findings.append(Finding(
                category="Headless Mode",
                severity="info",
                description="Using default headless mode (True). Good for production.",
                line=None,
                recommendation="No action needed. Default headless=True is correct.",
                weight=SEVERITY_WEIGHTS["info"],
            ))

    def _check_user_agent(self):
        """Check if a custom user agent is set."""
        has_ua = self._has_pattern(r"user_agent\s*=") or self._has_pattern(r"userAgent")
        has_ua_list = self._has_pattern(r"USER_AGENTS?\s*=\s*\[")
        has_random_ua = self._has_pattern(r"random\.choice.*(?:USER_AGENT|user_agent|ua)")

        if not has_ua:
            self.findings.append(Finding(
                category="User Agent",
                severity="critical",
                description="No custom user agent configured. Playwright's default user agent contains 'HeadlessChrome' which is trivially detected.",
                line=None,
                recommendation="Set a realistic user agent: context = await browser.new_context(user_agent='Mozilla/5.0 ...')",
                weight=SEVERITY_WEIGHTS["critical"],
            ))
        elif has_ua_list and has_random_ua:
            self.findings.append(Finding(
                category="User Agent",
                severity="info",
                description="User agent rotation detected. Good anti-detection practice.",
                line=self._find_line(r"USER_AGENTS?\s*=\s*\["),
                recommendation="Ensure user agents are recent and match the browser being launched (e.g., Chrome UA for Chromium).",
                weight=SEVERITY_WEIGHTS["info"],
            ))
        elif has_ua:
            self.findings.append(Finding(
                category="User Agent",
                severity="low",
                description="Custom user agent set but no rotation detected. Single user agent is fingerprint-able at scale.",
                line=self._find_line(r"user_agent\s*="),
                recommendation="Rotate through 5-10 recent user agents using random.choice().",
                weight=SEVERITY_WEIGHTS["low"],
            ))

    def _check_viewport(self):
        """Check viewport configuration."""
        has_viewport = self._has_pattern(r"viewport\s*=\s*\{") or self._has_pattern(r"viewport.*width")

        if not has_viewport:
            self.findings.append(Finding(
                category="Viewport Size",
                severity="high",
                description="No viewport configured. Default Playwright viewport (1280x720) is common among bots. Sites may flag unusual viewport distributions.",
                line=None,
                recommendation="Set a common desktop viewport: viewport={'width': 1920, 'height': 1080}. Vary across runs.",
                weight=SEVERITY_WEIGHTS["high"],
            ))
        else:
            # Check for suspiciously small viewports
            match = re.search(r"width['\"]?\s*[:=]\s*(\d+)", self.content)
            if match:
                width = int(match.group(1))
                if width < 1024:
                    self.findings.append(Finding(
                        category="Viewport Size",
                        severity="medium",
                        description=f"Viewport width {width}px is unusually small. Most desktop browsers are 1366px+ wide.",
                        line=self._find_line(r"width.*" + str(width)),
                        recommendation="Use 1366x768 (most common) or 1920x1080. Avoid unusual sizes like 800x600.",
                        weight=SEVERITY_WEIGHTS["medium"],
                    ))
                else:
                    self.findings.append(Finding(
                        category="Viewport Size",
                        severity="info",
                        description=f"Viewport width {width}px is reasonable.",
                        line=self._find_line(r"width.*" + str(width)),
                        recommendation="No action needed.",
                        weight=SEVERITY_WEIGHTS["info"],
                    ))

    def _check_webdriver_flag(self):
        """Check if navigator.webdriver is being removed."""
        has_webdriver_override = (
            self._has_pattern(r"navigator.*webdriver") or
            self._has_pattern(r"webdriver.*undefined") or
            self._has_pattern(r"add_init_script.*webdriver")
        )

        if not has_webdriver_override:
            self.findings.append(Finding(
                category="WebDriver Flag",
                severity="critical",
                description="navigator.webdriver is not overridden. This is the most common bot detection check. Every major anti-bot service tests this property.",
                line=None,
                recommendation=(
                    "Add init script to remove the flag:\n"
                    "  await page.add_init_script(\"Object.defineProperty(navigator, 'webdriver', {get: () => undefined});\")"
                ),
                weight=SEVERITY_WEIGHTS["critical"],
            ))
        else:
            self.findings.append(Finding(
                category="WebDriver Flag",
                severity="info",
                description="navigator.webdriver override detected.",
                line=self._find_line(r"webdriver"),
                recommendation="No action needed.",
                weight=SEVERITY_WEIGHTS["info"],
            ))

    def _check_navigator_properties(self):
        """Check for additional navigator property hardening."""
        checks = {
            "plugins": (r"navigator.*plugins", "navigator.plugins is empty in headless mode. Real browsers report installed plugins."),
            "languages": (r"navigator.*languages", "navigator.languages should be set to match the user agent locale."),
            "platform": (r"navigator.*platform", "navigator.platform should match the user agent OS."),
        }

        overridden_count = 0
        for prop, (pattern, desc) in checks.items():
            if self._has_pattern(pattern):
                overridden_count += 1

        if overridden_count == 0:
            self.findings.append(Finding(
                category="Navigator Properties",
                severity="medium",
                description="No navigator property hardening detected. Advanced anti-bot services check plugins, languages, and platform properties.",
                line=None,
                recommendation="Override navigator.plugins, navigator.languages, and navigator.platform via add_init_script() to match realistic browser fingerprints.",
                weight=SEVERITY_WEIGHTS["medium"],
            ))
        elif overridden_count < 3:
            self.findings.append(Finding(
                category="Navigator Properties",
                severity="low",
                description=f"Partial navigator hardening ({overridden_count}/3 properties). Consider covering all three: plugins, languages, platform.",
                line=None,
                recommendation="Add overrides for any missing properties among: plugins, languages, platform.",
                weight=SEVERITY_WEIGHTS["low"],
            ))

    def _check_request_delays(self):
        """Check for human-like request delays."""
        has_sleep = self._has_pattern(r"asyncio\.sleep") or self._has_pattern(r"wait_for_timeout")
        has_random_delay = (
            self._has_pattern(r"random\.(uniform|randint|random)") and has_sleep
        )

        if not has_sleep:
            self.findings.append(Finding(
                category="Request Timing",
                severity="high",
                description="No delays between actions detected. Machine-speed interactions are the easiest behavior-based detection signal.",
                line=None,
                recommendation="Add random delays between page interactions: await asyncio.sleep(random.uniform(0.5, 2.0))",
                weight=SEVERITY_WEIGHTS["high"],
            ))
        elif not has_random_delay:
            self.findings.append(Finding(
                category="Request Timing",
                severity="medium",
                description="Fixed delays detected but no randomization. Constant timing intervals are detectable patterns.",
                line=self._find_line(r"(asyncio\.sleep|wait_for_timeout)"),
                recommendation="Use random delays: random.uniform(min_seconds, max_seconds) instead of fixed values.",
                weight=SEVERITY_WEIGHTS["medium"],
            ))
        else:
            self.findings.append(Finding(
                category="Request Timing",
                severity="info",
                description="Randomized delays detected between actions.",
                line=self._find_line(r"random\.(uniform|randint)"),
                recommendation="No action needed. Ensure delays are realistic (0.5-3s for browsing, 1-5s for reading).",
                weight=SEVERITY_WEIGHTS["info"],
            ))

    def _check_error_handling(self):
        """Check for error handling patterns."""
        has_try_except = self._has_pattern(r"try\s*:") and self._has_pattern(r"except")
        has_retry = self._has_pattern(r"retr(y|ies)") or self._has_pattern(r"max_retries|max_attempts")

        if not has_try_except:
            self.findings.append(Finding(
                category="Error Handling",
                severity="medium",
                description="No try/except blocks found. Unhandled errors will crash the automation and leave browser instances running.",
                line=None,
                recommendation="Wrap page interactions in try/except. Handle TimeoutError, network errors, and element-not-found gracefully.",
                weight=SEVERITY_WEIGHTS["medium"],
            ))
        elif not has_retry:
            self.findings.append(Finding(
                category="Error Handling",
                severity="low",
                description="Error handling present but no retry logic detected. Transient failures (network blips, slow loads) will cause data loss.",
                line=None,
                recommendation="Add retry with exponential backoff for network operations and element interactions.",
                weight=SEVERITY_WEIGHTS["low"],
            ))

    def _check_proxy(self):
        """Check for proxy configuration."""
        has_proxy = self._has_pattern(r"proxy\s*=\s*\{") or self._has_pattern(r"proxy.*server")

        if not has_proxy:
            self.findings.append(Finding(
                category="Proxy",
                severity="low",
                description="No proxy configuration detected. Running from a single IP address is fine for small jobs but will trigger rate limits at scale.",
                line=None,
                recommendation="For high-volume scraping, use rotating proxies: proxy={'server': 'http://proxy:port'}",
                weight=SEVERITY_WEIGHTS["low"],
            ))

    def _check_session_management(self):
        """Check for session/cookie management."""
        has_storage_state = self._has_pattern(r"storage_state")
        has_cookies = self._has_pattern(r"cookies\(\)") or self._has_pattern(r"add_cookies")

        if not has_storage_state and not has_cookies:
            self.findings.append(Finding(
                category="Session Management",
                severity="low",
                description="No session persistence detected. Each run will start fresh, requiring re-authentication.",
                line=None,
                recommendation="Use storage_state() to save/restore sessions across runs. This avoids repeated logins that may trigger security alerts.",
                weight=SEVERITY_WEIGHTS["low"],
            ))

    def _check_browser_close(self):
        """Check if browser is properly closed."""
        has_close = self._has_pattern(r"browser\.close\(\)") or self._has_pattern(r"await.*close")
        has_context_manager = self._has_pattern(r"async\s+with\s+async_playwright")

        if not has_close and not has_context_manager:
            self.findings.append(Finding(
                category="Resource Cleanup",
                severity="medium",
                description="No browser.close() or context manager detected. Browser processes will leak on failure.",
                line=None,
                recommendation="Use 'async with async_playwright() as p:' or ensure browser.close() is in a finally block.",
                weight=SEVERITY_WEIGHTS["medium"],
            ))

    def _check_stealth_imports(self):
        """Check for stealth/anti-detection library usage."""
        has_stealth = self._has_pattern(r"playwright_stealth|stealth_async|undetected")
        if has_stealth:
            self.findings.append(Finding(
                category="Stealth Library",
                severity="info",
                description="Third-party stealth library detected. These provide additional fingerprint evasion but add dependencies.",
                line=self._find_line(r"playwright_stealth|stealth_async|undetected"),
                recommendation="Stealth libraries are helpful but not a silver bullet. Still implement manual checks for user agent, viewport, and timing.",
                weight=SEVERITY_WEIGHTS["info"],
            ))

    def get_risk_score(self) -> int:
        """Calculate overall risk score (0-100). Higher = more detectable."""
        raw_score = sum(f.weight for f in self.findings)
        # Cap at 100
        return min(raw_score, 100)

    def get_risk_level(self) -> str:
        """Get human-readable risk level."""
        score = self.get_risk_score()
        if score <= 10:
            return "LOW"
        elif score <= 30:
            return "MODERATE"
        elif score <= 50:
            return "HIGH"
        else:
            return "CRITICAL"

    def get_summary(self) -> dict:
        """Get a summary of the analysis."""
        severity_counts = {"critical": 0, "high": 0, "medium": 0, "low": 0, "info": 0}
        for f in self.findings:
            severity_counts[f.severity] += 1

        return {
            "file": self.file_path,
            "risk_score": self.get_risk_score(),
            "risk_level": self.get_risk_level(),
            "total_findings": len(self.findings),
            "severity_counts": severity_counts,
            "actionable_findings": len([f for f in self.findings if f.severity != "info"]),
        }


def format_text_report(checker: AntiDetectionChecker, verbose: bool = False) -> str:
    """Format findings as human-readable text."""
    lines = []
    summary = checker.get_summary()

    lines.append("=" * 60)
    lines.append("  ANTI-DETECTION AUDIT REPORT")
    lines.append("=" * 60)
    lines.append(f"File:          {summary['file']}")
    lines.append(f"Risk Score:    {summary['risk_score']}/100 ({summary['risk_level']})")
    lines.append(f"Total Issues:  {summary['actionable_findings']} actionable, {summary['severity_counts']['info']} info")
    lines.append("")

    # Severity breakdown
    for sev in ["critical", "high", "medium", "low"]:
        count = summary["severity_counts"][sev]
        if count > 0:
            lines.append(f"  {sev.upper():10s} {count}")
    lines.append("")

    # Findings grouped by severity
    severity_order = ["critical", "high", "medium", "low"]
    if verbose:
        severity_order.append("info")

    for sev in severity_order:
        sev_findings = [f for f in checker.findings if f.severity == sev]
        if not sev_findings:
            continue

        lines.append(f"--- {sev.upper()} ---")
        for f in sev_findings:
            line_info = f" (line {f.line})" if f.line else ""
            lines.append(f"  [{f.category}]{line_info}")
            lines.append(f"    {f.description}")
            lines.append(f"    Fix: {f.recommendation}")
            lines.append("")

    # Exit code guidance
    lines.append("-" * 60)
    score = summary["risk_score"]
    if score <= 10:
        lines.append("Result: PASS - Low detection risk.")
    elif score <= 30:
        lines.append("Result: PASS with warnings - Address medium/high issues for production use.")
    else:
        lines.append("Result: FAIL - High detection risk. Fix critical and high issues before deploying.")
    lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Audit a Playwright script for common bot detection vectors.",
        epilog=(
            "Examples:\n"
            "  %(prog)s --file scraper.py\n"
            "  %(prog)s --file scraper.py --verbose\n"
            "  %(prog)s --file scraper.py --json\n"
            "\n"
            "Exit codes:\n"
            "  0 - Low risk (score 0-10)\n"
            "  1 - Moderate to high risk (score 11-50)\n"
            "  2 - Critical risk (score 51+)\n"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--file",
        required=True,
        help="Path to the Playwright script to audit",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        dest="json_output",
        default=False,
        help="Output results as JSON",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        default=False,
        help="Include informational (non-actionable) findings in output",
    )

    args = parser.parse_args()

    file_path = os.path.abspath(args.file)
    if not os.path.isfile(file_path):
        print(f"Error: File not found: {file_path}", file=sys.stderr)
        sys.exit(2)

    try:
        with open(file_path, "r", encoding="utf-8") as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading file: {e}", file=sys.stderr)
        sys.exit(2)

    if not content.strip():
        print("Error: File is empty.", file=sys.stderr)
        sys.exit(2)

    checker = AntiDetectionChecker(content, file_path)
    checker.check_all()

    if args.json_output:
        output = checker.get_summary()
        output["findings"] = [asdict(f) for f in checker.findings]
        if not args.verbose:
            output["findings"] = [f for f in output["findings"] if f["severity"] != "info"]
        print(json.dumps(output, indent=2))
    else:
        print(format_text_report(checker, verbose=args.verbose))

    # Exit code based on risk
    score = checker.get_risk_score()
    if score <= 10:
        sys.exit(0)
    elif score <= 50:
        sys.exit(1)
    else:
        sys.exit(2)


if __name__ == "__main__":
    main()
