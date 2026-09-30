#!/usr/bin/env python3
"""
Phase 5: Generate an HTML evaluation report from evaluation_summary.json.

Produces a self-contained 3-tab HTML report:
  Tab 1: Coherence — codebase alignment details
  Tab 2: Effectiveness — blind test results (if available)
  Tab 3: Recommendations — actionable fixes

Usage:
    python -m scripts.generate_report <evaluation_summary.json> [--output <path>]
"""

import argparse
import json
from pathlib import Path

HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>CLAUDE.md Evaluation Report</title>
<style>
  :root {{
    --bg: #0d1117; --surface: #161b22; --border: #30363d;
    --text: #e6edf3; --muted: #8b949e; --accent: #58a6ff;
    --green: #3fb950; --red: #f85149; --yellow: #d29922; --purple: #bc8cff;
  }}
  * {{ margin: 0; padding: 0; box-sizing: border-box; }}
  body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif;
    background: var(--bg); color: var(--text); line-height: 1.6; padding: 2rem; }}
  .container {{ max-width: 960px; margin: 0 auto; }}

  /* Header */
  .header {{ text-align: center; margin-bottom: 2rem; padding: 2rem;
    background: var(--surface); border: 1px solid var(--border); border-radius: 12px; }}
  .header h1 {{ font-size: 1.6rem; margin-bottom: 0.5rem; }}
  .grade {{ display: inline-block; font-size: 3rem; font-weight: 700;
    width: 80px; height: 80px; line-height: 80px; border-radius: 50%;
    margin: 1rem 0; }}
  .grade-A {{ background: var(--green); color: #000; }}
  .grade-B {{ background: #238636; color: #fff; }}
  .grade-C {{ background: var(--yellow); color: #000; }}
  .grade-D {{ background: #da3633; color: #fff; }}
  .grade-F {{ background: var(--red); color: #fff; }}
  .score {{ font-size: 1.2rem; color: var(--muted); }}

  /* Tabs */
  .tabs {{ display: flex; gap: 0; margin-bottom: 0; }}
  .tab {{ padding: 0.75rem 1.5rem; cursor: pointer; border: 1px solid var(--border);
    border-bottom: none; border-radius: 8px 8px 0 0; background: var(--bg);
    color: var(--muted); font-weight: 500; transition: all 0.2s; }}
  .tab.active {{ background: var(--surface); color: var(--text); border-bottom-color: var(--surface); }}
  .tab-content {{ display: none; padding: 1.5rem; background: var(--surface);
    border: 1px solid var(--border); border-radius: 0 8px 8px 8px; }}
  .tab-content.active {{ display: block; }}

  /* Cards */
  .card {{ background: var(--bg); border: 1px solid var(--border); border-radius: 8px;
    padding: 1rem; margin-bottom: 1rem; }}
  .card h3 {{ font-size: 0.95rem; margin-bottom: 0.5rem; color: var(--accent); }}

  /* Stats */
  .stats {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(120px, 1fr)); gap: 1rem; margin-bottom: 1.5rem; }}
  .stat {{ text-align: center; padding: 1rem; background: var(--bg); border: 1px solid var(--border); border-radius: 8px; }}
  .stat-value {{ font-size: 1.8rem; font-weight: 700; }}
  .stat-label {{ font-size: 0.8rem; color: var(--muted); margin-top: 0.25rem; }}
  .stat-green .stat-value {{ color: var(--green); }}
  .stat-red .stat-value {{ color: var(--red); }}
  .stat-yellow .stat-value {{ color: var(--yellow); }}
  .stat-purple .stat-value {{ color: var(--purple); }}

  /* Issues */
  .issue {{ display: flex; gap: 0.75rem; align-items: flex-start; padding: 0.75rem; border-radius: 6px;
    margin-bottom: 0.5rem; background: var(--bg); border: 1px solid var(--border); }}
  .badge {{ font-size: 0.7rem; padding: 0.15rem 0.5rem; border-radius: 12px; font-weight: 600;
    text-transform: uppercase; white-space: nowrap; }}
  .badge-high {{ background: rgba(248, 81, 73, 0.2); color: var(--red); }}
  .badge-medium {{ background: rgba(210, 153, 34, 0.2); color: var(--yellow); }}
  .badge-low {{ background: rgba(139, 148, 158, 0.2); color: var(--muted); }}
  .issue-text {{ flex: 1; font-size: 0.9rem; }}
  .issue-suggestion {{ color: var(--green); font-size: 0.85rem; margin-top: 0.25rem; }}

  /* Recommendations */
  .rec-section {{ margin-bottom: 1.5rem; }}
  .rec-section h3 {{ margin-bottom: 0.75rem; }}
  .rec-item {{ padding: 0.5rem 0.75rem; margin-bottom: 0.4rem; font-size: 0.9rem;
    background: var(--bg); border-left: 3px solid; border-radius: 0 4px 4px 0; }}
  .rec-remove {{ border-color: var(--red); }}
  .rec-fix {{ border-color: var(--yellow); }}
  .rec-add {{ border-color: var(--green); }}
  .rec-strengthen {{ border-color: var(--purple); }}

  /* Blind test */
  .result-row {{ display: grid; grid-template-columns: 1fr 80px 80px 120px;
    gap: 0.5rem; padding: 0.6rem; font-size: 0.85rem; border-bottom: 1px solid var(--border); }}
  .result-header {{ font-weight: 600; color: var(--muted); text-transform: uppercase; font-size: 0.75rem; }}
  .win {{ color: var(--green); font-weight: 600; }}
  .loss {{ color: var(--red); font-weight: 600; }}
  .tie {{ color: var(--yellow); }}

  .empty-state {{ text-align: center; padding: 3rem; color: var(--muted); }}
  code {{ background: rgba(110, 118, 129, 0.2); padding: 0.15rem 0.4rem; border-radius: 4px; font-size: 0.85rem; }}
</style>
</head>
<body>
<div class="container">

  <!-- Header -->
  <div class="header">
    <h1>CLAUDE.md Evaluation Report</h1>
    <div class="grade grade-{grade_class}">{grade}</div>
    <div class="score">{score} / 100</div>
  </div>

  <!-- Tabs -->
  <div class="tabs">
    <div class="tab active" onclick="showTab('coherence')">Coherence</div>
    <div class="tab" onclick="showTab('effectiveness')">Effectiveness</div>
    <div class="tab" onclick="showTab('recommendations')">Recommendations</div>
  </div>

  <!-- Tab 1: Coherence -->
  <div id="coherence" class="tab-content active">
    <div class="stats">
      <div class="stat stat-green"><div class="stat-value">{verified}</div><div class="stat-label">Verified</div></div>
      <div class="stat stat-red"><div class="stat-value">{stale}</div><div class="stat-label">Stale</div></div>
      <div class="stat stat-yellow"><div class="stat-value">{partial}</div><div class="stat-label">Partial</div></div>
      <div class="stat stat-purple"><div class="stat-value">{unverifiable}</div><div class="stat-label">Unverifiable</div></div>
    </div>
    <div class="card">
      <h3>Coherence Score: {coherence_score}%</h3>
      <p style="color:var(--muted);font-size:0.9rem">
        Measures how well your CLAUDE.md matches the actual codebase.
        {total_claims} total claims extracted, {testable_claims} testable.
      </p>
    </div>
    {issues_html}
  </div>

  <!-- Tab 2: Effectiveness -->
  <div id="effectiveness" class="tab-content">
    {effectiveness_html}
  </div>

  <!-- Tab 3: Recommendations -->
  <div id="recommendations" class="tab-content">
    {recommendations_html}
  </div>

</div>

<script>
function showTab(id) {{
  document.querySelectorAll('.tab-content').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  document.getElementById(id).classList.add('active');
  event.target.classList.add('active');
}}
</script>
</body>
</html>"""


# ---------------------------------------------------------------------------
# HTML builders
# ---------------------------------------------------------------------------


def build_issues_html(issues: list[dict]) -> str:
    if not issues:
        return '<div class="card"><p style="color:var(--muted)">No issues found.</p></div>'

    html_parts = ['<h3 style="margin-bottom:0.75rem">Top Issues</h3>']
    for issue in issues:
        severity = issue.get("severity", "low")
        badge_class = f"badge-{severity}"
        suggestion = ""
        if issue.get("suggestion"):
            suggestion = f'<div class="issue-suggestion">Fix: {_escape(issue["suggestion"])}</div>'

        html_parts.append(f"""
    <div class="issue">
      <span class="badge {badge_class}">{severity}</span>
      <div class="issue-text">
        <code>{_escape(issue.get('claim_id', ''))}</code> {_escape(issue.get('issue', ''))}
        {suggestion}
      </div>
    </div>""")

    return "\n".join(html_parts)


def build_effectiveness_html(effectiveness: dict | None) -> str:
    if not effectiveness:
        return """<div class="empty-state">
      <p>No blind test results available.</p>
      <p style="margin-top:0.5rem;font-size:0.85rem">Run a Full Eval to get effectiveness data.</p>
    </div>"""

    wins = effectiveness.get("claude_md_wins", 0)
    ties = effectiveness.get("ties", 0)
    losses = effectiveness.get("losses", 0)
    delta = effectiveness.get("programmatic_delta", "+0%")
    score = effectiveness.get("score", 0)

    return f"""
    <div class="stats">
      <div class="stat stat-green"><div class="stat-value">{wins}</div><div class="stat-label">CLAUDE.md Wins</div></div>
      <div class="stat"><div class="stat-value">{ties}</div><div class="stat-label">Ties</div></div>
      <div class="stat stat-red"><div class="stat-value">{losses}</div><div class="stat-label">Losses</div></div>
    </div>
    <div class="card">
      <h3>Effectiveness Score: {score}%</h3>
      <p style="color:var(--muted);font-size:0.9rem">
        Blind test comparison: code with CLAUDE.md vs without.
        Programmatic check pass-rate delta: <strong>{delta}</strong>
      </p>
    </div>
    <div class="card">
      <h3>What This Means</h3>
      <p style="font-size:0.9rem">
        {"Your CLAUDE.md is highly effective — Claude produces noticeably better code when it has these instructions." if score >= 80
         else "Your CLAUDE.md shows moderate effectiveness — some conventions are followed better with instructions." if score >= 50
         else "Your CLAUDE.md shows limited effectiveness — consider revising conventions that don't change Claude's behavior."}
      </p>
    </div>"""


def build_recommendations_html(recommendations: dict) -> str:
    sections = []

    # Remove
    removes = recommendations.get("remove", [])
    if removes:
        items = "".join(f'<div class="rec-item rec-remove">Remove <code>{_escape(r)}</code> — vague/generic instruction</div>' for r in removes)
        sections.append(f'<div class="rec-section"><h3 style="color:var(--red)">Remove ({len(removes)})</h3>{items}</div>')

    # Fix
    fixes = recommendations.get("fix", [])
    if fixes:
        items = []
        for f in fixes:
            if isinstance(f, dict):
                items.append(f'<div class="rec-item rec-fix"><code>{_escape(f.get("claim_id", ""))}</code>: {_escape(f.get("suggested", ""))}</div>')
            else:
                items.append(f'<div class="rec-item rec-fix">{_escape(str(f))}</div>')
        sections.append(f'<div class="rec-section"><h3 style="color:var(--yellow)">Fix ({len(fixes)})</h3>{"".join(items)}</div>')

    # Add
    adds = recommendations.get("add", [])
    if adds:
        items = "".join(f'<div class="rec-item rec-add">{_escape(a)}</div>' for a in adds)
        sections.append(f'<div class="rec-section"><h3 style="color:var(--green)">Add ({len(adds)})</h3>{items}</div>')

    # Strengthen
    strengthens = recommendations.get("strengthen", [])
    if strengthens:
        items = "".join(f'<div class="rec-item rec-strengthen">{_escape(s)}</div>' for s in strengthens)
        sections.append(f'<div class="rec-section"><h3 style="color:var(--purple)">Strengthen ({len(strengthens)})</h3>{items}</div>')

    if not sections:
        return '<div class="empty-state"><p>No recommendations — your CLAUDE.md looks great!</p></div>'

    return "\n".join(sections)


def _escape(text: str) -> str:
    """Escape HTML special characters."""
    return (
        text.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


# ---------------------------------------------------------------------------
# Main report generation
# ---------------------------------------------------------------------------


def generate_report(summary: dict) -> str:
    """Generate full HTML report from evaluation_summary.json."""
    grade = summary.get("grade", "?")
    score = summary.get("overall_score", 0)
    coherence = summary.get("coherence", {})

    grade_class = grade if grade in ("A", "B", "C", "D", "F") else "F"

    return HTML_TEMPLATE.format(
        grade=grade,
        grade_class=grade_class,
        score=score,
        verified=coherence.get("verified", 0),
        stale=coherence.get("stale", 0),
        partial=coherence.get("partial", 0),
        unverifiable=coherence.get("unverifiable", 0),
        coherence_score=coherence.get("score", 0),
        total_claims=coherence.get("total_claims", 0),
        testable_claims=coherence.get("verified", 0) + coherence.get("stale", 0) + coherence.get("partial", 0),
        issues_html=build_issues_html(summary.get("top_issues", [])),
        effectiveness_html=build_effectiveness_html(summary.get("effectiveness")),
        recommendations_html=build_recommendations_html(summary.get("recommendations", {})),
    )


def main():
    parser = argparse.ArgumentParser(description="Generate HTML evaluation report")
    parser.add_argument("summary_json", type=Path, help="Path to evaluation_summary.json")
    parser.add_argument("--output", type=Path, default=None, help="Output HTML path (default: /tmp/claude-md-eval.html)")
    args = parser.parse_args()

    summary = json.loads(args.summary_json.read_text(encoding="utf-8"))
    html = generate_report(summary)

    output_path = args.output or Path("/tmp/claude-md-eval.html")
    output_path.write_text(html, encoding="utf-8")
    print(f"Report generated → {output_path}")
    print(f"Grade: {summary.get('grade', '?')} ({summary.get('overall_score', 0)}/100)")


if __name__ == "__main__":
    main()
