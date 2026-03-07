#!/usr/bin/env python3
"""
Audit Flow CLI - Helper script for audit-flow skill.

Usage:
    python audit.py init                          # Initialize database
    python audit.py list                          # List all sessions
    python audit.py show <session>                # Show session with flows
    python audit.py show <session> <flow>         # Show specific flow
    python audit.py export <session> [fmt]        # Export all flows
    python audit.py export <session> <flow> [fmt] # Export specific flow
    python audit.py csv-export                    # Export DB tables to .audit/csv/
    python audit.py csv-import                    # Import .audit/csv/ into DB
    python audit.py csv-merge <theirs_dir>        # Merge theirs CSVs into ours
"""

import argparse
import csv
import json
import os
import sqlite3
import subprocess
import sys
from collections import defaultdict, deque
from datetime import datetime
from pathlib import Path


def get_git_context():
    """Get current git context (commit, branch, dirty state)."""
    try:
        commit = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True
        ).stdout.strip()[:8]  # Short hash
    except subprocess.CalledProcessError:
        commit = None

    try:
        branch = subprocess.run(
            ["git", "branch", "--show-current"],
            capture_output=True, text=True, check=True
        ).stdout.strip()
    except subprocess.CalledProcessError:
        branch = None

    try:
        status = subprocess.run(
            ["git", "status", "--porcelain"],
            capture_output=True, text=True, check=True
        ).stdout.strip()
        dirty = 1 if status else 0
    except subprocess.CalledProcessError:
        dirty = 0

    return {"commit": commit, "branch": branch, "dirty": dirty}

# Optional YAML support
try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False

# Paths
AUDIT_DIR = Path(".audit")
DB_PATH = AUDIT_DIR / "audit.db"
CSV_DIR = AUDIT_DIR / "csv"
EXPORTS_DIR = Path("docs/audits")
SCHEMA_PATH = Path(__file__).parent.parent / "schema.sql"

# Table definitions: ordered columns for deterministic CSV output.
# Order matches schema.sql CREATE TABLE column order.
TABLE_COLUMNS = {
    "sessions": [
        "id", "name", "purpose", "description", "granularity",
        "git_commit", "git_branch", "git_dirty",
        "created_at", "updated_at", "status",
    ],
    "flows": [
        "id", "session_id", "name", "entry_point", "description",
        "created_at", "status",
    ],
    "tuples": [
        "id", "flow_id", "timestamp", "layer", "action", "subject",
        "file_ref", "props", "notes", "status",
    ],
    "edges": [
        "id", "from_tuple", "to_tuple", "relation", "condition",
        "props", "created_at",
    ],
    "findings": [
        "id", "session_id", "flow_id", "severity", "category",
        "description", "tuple_refs", "status", "created_at", "updated_at",
    ],
}

# Primary key column name per table (used for sorting in CSV export).
TABLE_PK = {
    "sessions": "id",
    "flows": "id",
    "tuples": "id",
    "edges": "id",
    "findings": "id",
}


def get_db():
    """Get database connection."""
    if not DB_PATH.exists():
        print(f"Error: Database not found at {DB_PATH}", file=sys.stderr)
        print("Run: python audit.py init", file=sys.stderr)
        sys.exit(1)
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    return conn


def cmd_init(args):
    """Initialize the database."""
    AUDIT_DIR.mkdir(exist_ok=True)

    if DB_PATH.exists() and not args.force:
        print(f"Database already exists at {DB_PATH}")
        print("Use --force to reinitialize (WARNING: deletes existing data)")
        return

    if args.force and DB_PATH.exists():
        DB_PATH.unlink()
        print("Removed existing database")

    conn = sqlite3.connect(DB_PATH)
    with open(SCHEMA_PATH) as f:
        conn.executescript(f.read())
    conn.close()
    print(f"Initialized database at {DB_PATH}")


def cmd_list(args):
    """List all sessions."""
    conn = get_db()
    cur = conn.execute("SELECT * FROM v_session_summary ORDER BY created_at DESC")

    rows = cur.fetchall()
    if not rows:
        print("No sessions found")
        return

    print(f"{'Name':<25} {'Purpose':<15} {'Status':<10} {'Flows':<6} {'Tuples':<8} {'Findings':<10} {'Created'}")
    print("-" * 105)
    for row in rows:
        print(f"{row['name']:<25} {row['purpose']:<15} {row['status']:<10} {row['flow_count']:<6} {row['tuple_count']:<8} {row['finding_count']:<10} {row['created_at']}")


def cmd_show(args):
    """Show session or flow details."""
    conn = get_db()

    # Get session
    session = conn.execute(
        "SELECT * FROM sessions WHERE name = ? OR id = ?",
        (args.session, args.session)
    ).fetchone()

    if not session:
        print(f"Session not found: {args.session}", file=sys.stderr)
        sys.exit(1)

    # If flow specified, show just that flow
    if args.flow:
        flow = conn.execute(
            "SELECT * FROM flows WHERE session_id = ? AND name = ?",
            (session['id'], args.flow)
        ).fetchone()

        if not flow:
            print(f"Flow not found: {args.flow}", file=sys.stderr)
            sys.exit(1)

        show_flow_details(conn, flow, session)
        return

    # Show session overview
    print(f"\n=== Session: {session['name']} ===")
    print(f"Purpose: {session['purpose']}")
    print(f"Granularity: {session['granularity']}")
    print(f"Status: {session['status']}")
    print(f"Created: {session['created_at']}")

    # List flows
    flows = conn.execute(
        "SELECT * FROM v_flow_summary WHERE session_id = ? ORDER BY created_at",
        (session['id'],)
    ).fetchall()

    if flows:
        print(f"\n=== Flows ({len(flows)}) ===")
        print(f"{'Name':<25} {'Entry Point':<35} {'Tuples':<8} {'Concerns':<10} {'Status'}")
        print("-" * 95)
        for f in flows:
            print(f"{f['name']:<25} {f['entry_point'][:35]:<35} {f['tuple_count']:<8} {f['concern_count']:<10} {f['status']}")

    # Show findings summary
    findings = conn.execute("""
        SELECT severity, COUNT(*) as count
        FROM findings WHERE session_id = ?
        GROUP BY severity
        ORDER BY CASE severity
            WHEN 'critical' THEN 1 WHEN 'high' THEN 2
            WHEN 'medium' THEN 3 WHEN 'low' THEN 4 ELSE 5
        END
    """, (session['id'],)).fetchall()

    if findings:
        print(f"\n=== Findings Summary ===")
        for f in findings:
            print(f"  {f['severity'].upper()}: {f['count']}")


def show_flow_details(conn, flow, session):
    """Show detailed flow information."""
    print(f"\n=== Flow: {flow['name']} ===")
    print(f"Session: {session['name']}")
    print(f"Entry Point: {flow['entry_point']}")
    print(f"Status: {flow['status']}")
    print(f"Created: {flow['created_at']}")

    # Get tuples
    tuples = conn.execute("""
        SELECT id, layer, action, subject, file_ref, status
        FROM tuples
        WHERE flow_id = ? AND status != 'deleted'
        ORDER BY timestamp
    """, (flow['id'],)).fetchall()

    if tuples:
        print(f"\n=== Tuples ({len(tuples)}) ===")
        print(f"{'ID':<5} {'Layer':<8} {'Action':<25} {'Subject':<30} {'Status'}")
        print("-" * 80)
        for t in tuples:
            print(f"{t['id']:<5} {t['layer']:<8} {t['action']:<25} {t['subject']:<30} {t['status']}")

    # Get edges
    edges = conn.execute("""
        SELECT e.*, t1.action as from_action, t2.action as to_action
        FROM edges e
        JOIN tuples t1 ON e.from_tuple = t1.id
        JOIN tuples t2 ON e.to_tuple = t2.id
        WHERE t1.flow_id = ?
    """, (flow['id'],)).fetchall()

    if edges:
        print(f"\n=== Edges ({len(edges)}) ===")
        for e in edges:
            cond = f" [{e['condition']}]" if e['condition'] else ""
            print(f"  {e['from_action']} --{e['relation']}{cond}--> {e['to_action']}")

    # Check for branch/merge points
    branch_merge = conn.execute("""
        SELECT * FROM v_branch_merge_points WHERE flow_name = ?
    """, (flow['name'],)).fetchall()

    if branch_merge:
        print(f"\n=== Non-Linear Points ===")
        for bm in branch_merge:
            print(f"  [{bm['node_type'].upper()}] {bm['action']} (in:{bm['incoming_edges']}, out:{bm['outgoing_edges']})")

    # Get findings for this flow
    findings = conn.execute("""
        SELECT id, severity, category, description, status
        FROM findings
        WHERE flow_id = ?
        ORDER BY CASE severity
            WHEN 'critical' THEN 1 WHEN 'high' THEN 2
            WHEN 'medium' THEN 3 WHEN 'low' THEN 4 ELSE 5
        END
    """, (flow['id'],)).fetchall()

    if findings:
        print(f"\n=== Findings ({len(findings)}) ===")
        for f in findings:
            print(f"[{f['severity'].upper()}] {f['category']}: {f['description']}")


def get_flow_data(conn, flow_id):
    """Get full flow data as dict."""
    flow = conn.execute("SELECT * FROM flows WHERE id = ?", (flow_id,)).fetchone()
    if not flow:
        return None

    tuples = conn.execute("""
        SELECT id, layer, action, subject, file_ref, props, notes, status, timestamp
        FROM tuples WHERE flow_id = ? AND status != 'deleted'
        ORDER BY timestamp
    """, (flow_id,)).fetchall()

    edges = conn.execute("""
        SELECT e.from_tuple, e.to_tuple, e.relation, e.condition, e.props
        FROM edges e
        JOIN tuples t ON e.from_tuple = t.id
        WHERE t.flow_id = ?
    """, (flow_id,)).fetchall()

    findings = conn.execute("""
        SELECT id, severity, category, description, tuple_refs, status
        FROM findings WHERE flow_id = ?
    """, (flow_id,)).fetchall()

    return {
        "flow": dict(flow),
        "tuples": [dict(t) for t in tuples],
        "edges": [dict(e) for e in edges],
        "findings": [dict(f) for f in findings]
    }


def get_session_data(conn, session_name):
    """Get full session data with all flows."""
    session = conn.execute(
        "SELECT * FROM sessions WHERE name = ? OR id = ?",
        (session_name, session_name)
    ).fetchone()

    if not session:
        return None

    flows = conn.execute(
        "SELECT id FROM flows WHERE session_id = ?",
        (session['id'],)
    ).fetchall()

    flow_data = []
    for f in flows:
        fd = get_flow_data(conn, f['id'])
        if fd:
            flow_data.append(fd)

    # Session-level findings (not associated with specific flow)
    session_findings = conn.execute("""
        SELECT id, severity, category, description, tuple_refs, status
        FROM findings WHERE session_id = ? AND flow_id IS NULL
    """, (session['id'],)).fetchall()

    return {
        "session": dict(session),
        "flows": flow_data,
        "session_findings": [dict(f) for f in session_findings]
    }


def export_json(data, output_path):
    """Export to JSON."""
    with open(output_path, "w") as f:
        json.dump(data, f, indent=2, default=str)
    print(f"  Exported: {output_path}")


def export_yaml(data, output_path):
    """Export to YAML."""
    if not HAS_YAML:
        print("  Skipped YAML: PyYAML not installed (pip install pyyaml)")
        return

    with open(output_path, "w") as f:
        yaml.dump(data, f, default_flow_style=False, sort_keys=False)
    print(f"  Exported: {output_path}")


def build_graph(tuples, edges):
    """Build adjacency list and in-degree map from edges."""
    tuple_ids = {t["id"] for t in tuples}
    adj = defaultdict(list)
    in_degree = {tid: 0 for tid in tuple_ids}
    for e in edges:
        src, dst = e["from_tuple"], e["to_tuple"]
        if src in tuple_ids and dst in tuple_ids:
            adj[src].append((dst, e))
            in_degree[dst] = in_degree.get(dst, 0) + 1
            in_degree.setdefault(src, 0)
    return adj, in_degree


def find_entry_nodes(tuples, edges, flow_entry_point=None):
    """Find entry nodes (zero in-degree), prioritize matching flow entry_point."""
    _, in_degree = build_graph(tuples, edges)
    zero_in = [tid for tid, deg in in_degree.items() if deg == 0]
    if flow_entry_point:
        ep_lower = flow_entry_point.lower()
        tuple_map = {t["id"]: t for t in tuples}
        for tid in zero_in:
            t = tuple_map.get(tid)
            if t and (ep_lower in t["action"].lower() or ep_lower in t.get("subject", "").lower()):
                zero_in.remove(tid)
                zero_in.insert(0, tid)
                break
    if not zero_in and tuples:
        zero_in = [tuples[0]["id"]]
    return zero_in


def topological_order(tuples, edges, entry_nodes):
    """BFS topological sort from entry nodes. Returns {tuple_id: step_number}."""
    adj, _ = build_graph(tuples, edges)
    tuple_ids = {t["id"] for t in tuples}
    order = {}
    visited = set()
    queue = deque()
    for nid in entry_nodes:
        if nid not in visited:
            visited.add(nid)
            queue.append(nid)
    step = 1
    while queue:
        nid = queue.popleft()
        order[nid] = step
        step += 1
        for neighbour, _ in adj.get(nid, []):
            if neighbour not in visited:
                visited.add(neighbour)
                queue.append(neighbour)
    # Unreached nodes (cycles, disconnected) get appended
    for tid in tuple_ids:
        if tid not in order:
            order[tid] = step
            step += 1
    return order


def classify_nodes(tuples, edges):
    """Separate (flow_nodes, observation_nodes).

    Observation = concern status + all parents also concerns (or no parents).
    Pure analyst notes chained by VALIDATES without real flow parents.
    """
    tuple_map = {t["id"]: t for t in tuples}
    tuple_ids = {t["id"] for t in tuples}
    parents = defaultdict(set)
    for e in edges:
        src, dst = e["from_tuple"], e["to_tuple"]
        if src in tuple_ids and dst in tuple_ids:
            parents[dst].add(src)
    observation_ids = set()
    for t in tuples:
        if t["status"] != "concern":
            continue
        parent_ids = parents.get(t["id"], set())
        if not parent_ids:
            observation_ids.add(t["id"])
            continue
        all_parents_concern = all(
            tuple_map[pid]["status"] == "concern"
            for pid in parent_ids if pid in tuple_map
        )
        if all_parents_concern:
            observation_ids.add(t["id"])
    flow_nodes = [t for t in tuples if t["id"] not in observation_ids]
    obs_nodes = [t for t in tuples if t["id"] in observation_ids]
    return flow_nodes, obs_nodes


def sanitize_mermaid_label(text):
    """Sanitize text for safe use in Mermaid node labels using HTML entities.

    Replaces problematic characters with HTML entities that Mermaid handles safely
    in quoted contexts: " < > ( ) | [ ]
    """
    replacements = {
        '"': '&quot;',
        '<': '&lt;',
        '>': '&gt;',
        '(': '&#40;',
        ')': '&#41;',
        '|': '&#124;',
        '[': '&#91;',
        ']': '&#93;',
    }
    result = text
    for char, entity in replacements.items():
        result = result.replace(char, entity)
    return result


def deduplicate_labels(tuples):
    """Return {tuple_id: label} with subject suffix when action is ambiguous."""
    action_counts = defaultdict(int)
    for t in tuples:
        action_counts[t["action"]] += 1
    labels = {}
    for t in tuples:
        label = t["action"]
        if action_counts[label] > 1:
            label = f"{label} ({t.get('subject', '')})"
        labels[t["id"]] = sanitize_mermaid_label(label)
    return labels


EDGE_ARROWS = {
    "TRIGGERS": "-->",
    "READS": "-.->",
    "WRITES": "==>",
    "VALIDATES": "-->",
    "TRANSFORMS": "-->",
    "BRANCHES": "-->",
    "MERGES": "-->",
}


def export_mermaid_flow(flow_data, output_path, direction="TD"):
    """Export single flow to Mermaid flowchart with step ordering and styled edges."""
    tuples = flow_data["tuples"]
    edges = flow_data["edges"]
    flow = flow_data.get("flow", {})

    if not tuples:
        print(f"  Skipped (no tuples): {output_path}")
        return

    # Classify nodes into flow vs observation
    flow_nodes, observation_nodes = classify_nodes(tuples, edges)

    # Compute step order from entry points
    entry_nodes = find_entry_nodes(tuples, edges, flow.get("entry_point"))
    step_order = topological_order(tuples, edges, entry_nodes)
    entry_set = set(entry_nodes)

    # Deduplicate labels
    labels = deduplicate_labels(tuples)

    # Build tuple ID map
    tuple_map = {t["id"]: f"T{t['id']}" for t in tuples}

    # Group flow nodes by layer
    layers = {}
    for t in flow_nodes:
        layer = t["layer"]
        if layer not in layers:
            layers[layer] = []
        layers[layer].append(t)

    # Sort each layer by step number
    for layer in layers:
        layers[layer].sort(key=lambda t: step_order.get(t["id"], 9999))

    lines = [f"flowchart {direction}"]

    # Flow subgraphs by layer
    for layer_name in ["CODE", "API", "AUTH", "NETWORK", "DATA"]:
        if layer_name not in layers:
            continue
        lines.append(f"    subgraph {layer_name}")
        for t in layers[layer_name]:
            node_id = tuple_map[t["id"]]
            step = step_order.get(t["id"], "?")
            label = f'{step}. {labels[t["id"]]}'
            if t["id"] in entry_set:
                lines.append(f'        {node_id}(["{label}"]):::entryPoint')
            elif t["status"] == "concern":
                lines.append(f'        {node_id}["{label}"]:::concern')
            else:
                lines.append(f'        {node_id}["{label}"]')
        lines.append("    end")

    # Observation subgraph
    if observation_nodes:
        lines.append("    subgraph OBSERVATIONS")
        lines.append("    style OBSERVATIONS stroke-dasharray: 5 5,fill:#fff9db,stroke:#fab005")
        for t in sorted(observation_nodes, key=lambda t: step_order.get(t["id"], 9999)):
            node_id = tuple_map[t["id"]]
            step = step_order.get(t["id"], "?")
            label = f'{step}. {labels[t["id"]]}'
            lines.append(f'        {node_id}["{label}"]:::observation')
        lines.append("    end")

    lines.append("")

    # Edges with relation-specific arrows
    for e in edges:
        from_id = tuple_map.get(e["from_tuple"])
        to_id = tuple_map.get(e["to_tuple"])
        if from_id and to_id:
            arrow = EDGE_ARROWS.get(e["relation"], "-->")
            relation = e["relation"]
            if e.get("condition"):
                label = f"{relation}<br/>{sanitize_mermaid_label(e['condition'])}"
            else:
                label = relation
            lines.append(f'    {from_id} {arrow}|"{label}"| {to_id}')

    # Styles
    lines.extend([
        "",
        "    classDef concern fill:#ff6b6b,stroke:#c92a2a",
        "    classDef entryPoint fill:#51cf66,stroke:#2b8a3e",
        "    classDef observation fill:#fff9db,stroke:#fab005,stroke-dasharray: 5 5",
    ])

    with open(output_path, "w") as f:
        f.write("\n".join(lines))
    print(f"  Exported: {output_path}")


def export_markdown_flow(flow_data, session_name, output_path, session_data=None):
    """Export single flow to Markdown report."""
    flow = flow_data["flow"]
    tuples = flow_data["tuples"]
    findings = flow_data["findings"]

    lines = [
        f"# {flow['name']}",
        "",
        f"**Session:** {session_name}",
        f"**Entry Point:** {flow['entry_point']}",
        f"**Status:** {flow['status']}",
        f"**Created:** {flow['created_at']}",
    ]

    # Add git context if available
    if session_data and session_data.get("session"):
        session = session_data["session"]
        if session.get("git_commit"):
            git_dirty = "No" if not session.get("git_dirty") else "Yes"
            lines.extend([
                "",
                "**Git Context:**",
                f"- Commit: `{session['git_commit']}` ({session.get('git_branch', 'unknown')})",
                f"- Uncommitted changes: {git_dirty}",
            ])

    lines.extend([
        "",
        "## Flow Steps",
        "",
        "| # | Layer | Action | Subject | File | Status |",
        "|---|-------|--------|---------|------|--------|",
    ])

    for t in tuples:
        file_ref = t.get("file_ref") or "-"
        lines.append(f"| {t['id']} | {t['layer']} | {t['action']} | {t['subject']} | {file_ref} | {t['status']} |")

    if findings:
        lines.extend(["", "## Findings", ""])

        by_severity = {}
        for f in findings:
            sev = f["severity"]
            if sev not in by_severity:
                by_severity[sev] = []
            by_severity[sev].append(f)

        for sev in ["critical", "high", "medium", "low", "info"]:
            if sev in by_severity:
                lines.append(f"### {sev.title()}")
                lines.append("")
                for f in by_severity[sev]:
                    lines.append(f"- **{f['category']}**: {f['description']}")
                lines.append("")

    lines.extend(["", "## Flow Diagram", "", f"See [{flow['name']}.mermaid]({flow['name']}.mermaid)"])

    with open(output_path, "w") as f:
        f.write("\n".join(lines))
    print(f"  Exported: {output_path}")


def cmd_validate(args):
    """Validate session flows for common issues."""
    conn = get_db()

    session = conn.execute(
        "SELECT * FROM sessions WHERE name = ? OR id = ?",
        (args.session, args.session)
    ).fetchone()

    if not session:
        print(f"Session not found: {args.session}", file=sys.stderr)
        sys.exit(1)

    flows = conn.execute(
        "SELECT id, name FROM flows WHERE session_id = ?",
        (session['id'],)
    ).fetchall()

    errors = 0
    warnings = 0

    for flow in flows:
        flow_data = get_flow_data(conn, flow['id'])
        if not flow_data:
            continue

        tuples = flow_data["tuples"]
        edges = flow_data["edges"]
        flow_name = flow['name']

        print(f"\n=== Validating: {flow_name} ===")

        # Check 1: BRANCHES edges must have conditions
        for e in edges:
            if e["relation"] == "BRANCHES" and not e.get("condition"):
                from_t = next((t for t in tuples if t["id"] == e["from_tuple"]), None)
                to_t = next((t for t in tuples if t["id"] == e["to_tuple"]), None)
                from_label = from_t["action"] if from_t else f"T{e['from_tuple']}"
                to_label = to_t["action"] if to_t else f"T{e['to_tuple']}"
                print(f"  ERROR: BRANCHES without condition: {from_label} -> {to_label}")
                errors += 1

        # Check 2: Orphan nodes (no edges)
        connected = set()
        for e in edges:
            connected.add(e["from_tuple"])
            connected.add(e["to_tuple"])
        for t in tuples:
            if t["id"] not in connected:
                print(f"  WARN: Orphan node: T{t['id']} ({t['action']})")
                warnings += 1

        # Check 3: Duplicate labels without subject disambiguation
        action_counts = {}
        for t in tuples:
            action_counts[t["action"]] = action_counts.get(t["action"], 0) + 1
        for action, count in action_counts.items():
            if count > 1:
                dupes = [t for t in tuples if t["action"] == action]
                subjects = [t.get("subject", "") for t in dupes]
                if len(set(subjects)) <= 1:
                    print(f'  WARN: Duplicate label ({count}x): "{action}" -- add distinct subjects')
                    warnings += 1

        # Check 4: Node count
        node_count = len(tuples)
        if node_count >= 60:
            print(f"  ERROR: {node_count} nodes -- split into sub-flows (max recommended: 40)")
            errors += 1
        elif node_count >= 40:
            print(f"  WARN: {node_count} nodes -- consider splitting (recommended: <40)")
            warnings += 1

        # Check 5: Entry point detectable
        entry_nodes = find_entry_nodes(tuples, edges)
        if not entry_nodes:
            print(f"  WARN: No entry point detected (all nodes have incoming edges)")
            warnings += 1
        else:
            entry_labels = [
                next((t["action"] for t in tuples if t["id"] == eid), f"T{eid}")
                for eid in entry_nodes
            ]
            print(f"  OK: Entry point(s): {', '.join(entry_labels)}")

        if errors == 0 and warnings == 0:
            print(f"  OK: No issues found ({node_count} nodes)")

    print(f"\n=== Summary: {errors} errors, {warnings} warnings ===")
    if errors > 0:
        sys.exit(1)


def cmd_export(args):
    """Export session or specific flow."""
    conn = get_db()

    # Get session
    session = conn.execute(
        "SELECT * FROM sessions WHERE name = ? OR id = ?",
        (args.session, args.session)
    ).fetchone()

    if not session:
        print(f"Session not found: {args.session}", file=sys.stderr)
        sys.exit(1)

    session_name = session["name"]
    output_dir = EXPORTS_DIR / session_name
    output_dir.mkdir(parents=True, exist_ok=True)

    fmt = args.format.lower()

    # Export specific flow or all flows
    if args.flow:
        flow = conn.execute(
            "SELECT * FROM flows WHERE session_id = ? AND name = ?",
            (session['id'], args.flow)
        ).fetchone()

        if not flow:
            print(f"Flow not found: {args.flow}", file=sys.stderr)
            sys.exit(1)

        flow_data = get_flow_data(conn, flow['id'])
        print(f"Exporting flow '{args.flow}' to {output_dir}/")

        if fmt in ("json", "all"):
            export_json(flow_data, output_dir / f"{args.flow}.json")
        if fmt in ("yaml", "all"):
            export_yaml(flow_data, output_dir / f"{args.flow}.yaml")
        if fmt in ("mermaid", "all"):
            export_mermaid_flow(flow_data, output_dir / f"{args.flow}.mermaid", args.direction)
        if fmt in ("md", "markdown", "all"):
            export_markdown_flow(flow_data, session_name, output_dir / f"{args.flow}.md")

    else:
        # Export full session
        session_data = get_session_data(conn, args.session)
        print(f"Exporting session '{session_name}' to {output_dir}/")

        if fmt in ("json", "all"):
            export_json(session_data, output_dir / "session.json")
        if fmt in ("yaml", "all"):
            export_yaml(session_data, output_dir / "session.yaml")

        # Export each flow's mermaid and markdown
        for flow_data in session_data["flows"]:
            flow_name = flow_data["flow"]["name"]
            if fmt in ("mermaid", "all"):
                export_mermaid_flow(flow_data, output_dir / f"{flow_name}.mermaid", args.direction)
            if fmt in ("md", "markdown", "all"):
                export_markdown_flow(flow_data, session_name, output_dir / f"{flow_name}.md", session_data)

        # Export session-level summary
        if fmt in ("md", "markdown", "all"):
            export_session_summary(session_data, output_dir / "README.md")

    print("Done!")


def export_session_summary(session_data, output_path):
    """Export session summary as README."""
    session = session_data["session"]
    flows = session_data["flows"]

    lines = [
        f"# {session['name']}",
        "",
        f"**Purpose:** {session['purpose']}",
        f"**Granularity:** {session['granularity']}",
        f"**Status:** {session['status']}",
        f"**Created:** {session['created_at']}",
    ]

    # Add git context if available
    if session.get("git_commit"):
        git_dirty = "No" if not session.get("git_dirty") else "Yes"
        lines.extend([
            "",
            "**Git Context:**",
            f"- Commit: `{session['git_commit']}` ({session.get('git_branch', 'unknown')})",
            f"- Uncommitted changes: {git_dirty}",
        ])

    lines.extend([
        "",
        "## Flows",
        "",
    ])

    for fd in flows:
        flow = fd["flow"]
        tuple_count = len(fd["tuples"])
        finding_count = len(fd["findings"])
        lines.append(f"- [{flow['name']}]({flow['name']}.md) - {tuple_count} steps, {finding_count} findings")

    if session_data.get("session_findings"):
        lines.extend(["", "## Session-Level Findings", ""])
        for f in session_data["session_findings"]:
            lines.append(f"- [{f['severity'].upper()}] {f['category']}: {f['description']}")

    with open(output_path, "w") as f:
        f.write("\n".join(lines))
    print(f"  Exported: {output_path}")


# ---------------------------------------------------------------------------
# CSV intermediate format commands
# ---------------------------------------------------------------------------

def _read_csv_table(csv_path):
    """Read a CSV file and return list of dicts (one per row)."""
    with open(csv_path, newline="") as f:
        reader = csv.DictReader(f)
        return list(reader)


def _write_csv_table(rows, columns, csv_path):
    """Write rows (list of dicts) to a CSV file with explicit column order."""
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=columns, quoting=csv.QUOTE_ALL)
        writer.writeheader()
        writer.writerows(rows)


def _pk_sort_key(table_name):
    """Return a sort key function for deterministic PK ordering."""
    pk = TABLE_PK[table_name]
    def _key(row):
        val = row.get(pk, "")
        # INTEGER PKs should sort numerically
        if table_name != "sessions":
            try:
                return int(val)
            except (ValueError, TypeError):
                return 0
        return str(val)
    return _key


def cmd_csv_export(args):
    """Export all database tables to CSV files in .audit/csv/."""
    conn = get_db()
    CSV_DIR.mkdir(parents=True, exist_ok=True)

    for table_name, columns in TABLE_COLUMNS.items():
        rows = conn.execute(
            f"SELECT {', '.join(columns)} FROM {table_name}"
        ).fetchall()
        dict_rows = [dict(zip(columns, row)) for row in rows]
        # Convert None values to empty string for CSV compatibility
        for row in dict_rows:
            for col in columns:
                if row[col] is None:
                    row[col] = ""
        # Sort by primary key for deterministic git diffs
        dict_rows.sort(key=_pk_sort_key(table_name))
        csv_path = CSV_DIR / f"{table_name}.csv"
        _write_csv_table(dict_rows, columns, csv_path)
        print(f"  Exported {len(dict_rows):>4} rows -> {csv_path}")

    conn.close()
    print("CSV export complete.")


def cmd_csv_import(args):
    """Import CSV files from .audit/csv/ into the database, replacing all contents."""
    if not CSV_DIR.exists():
        print(f"Error: CSV directory not found at {CSV_DIR}", file=sys.stderr)
        print("Run: python audit.py csv-export", file=sys.stderr)
        sys.exit(1)

    # Verify all CSV files exist before touching the database
    for table_name in TABLE_COLUMNS:
        csv_path = CSV_DIR / f"{table_name}.csv"
        if not csv_path.exists():
            print(f"Error: Missing CSV file: {csv_path}", file=sys.stderr)
            sys.exit(1)

    # Recreate database from schema
    if DB_PATH.exists():
        DB_PATH.unlink()
    conn = sqlite3.connect(DB_PATH)
    with open(SCHEMA_PATH) as f:
        conn.executescript(f.read())

    # Import order matters for foreign keys: parents before children
    import_order = ["sessions", "flows", "tuples", "edges", "findings"]

    for table_name in import_order:
        csv_path = CSV_DIR / f"{table_name}.csv"
        rows = _read_csv_table(csv_path)
        columns = TABLE_COLUMNS[table_name]

        if not rows:
            print(f"  Imported    0 rows <- {csv_path}")
            continue

        placeholders = ", ".join(["?"] * len(columns))
        col_list = ", ".join(columns)
        insert_sql = f"INSERT INTO {table_name} ({col_list}) VALUES ({placeholders})"

        for row in rows:
            values = []
            for col in columns:
                val = row.get(col, "")
                # Convert empty strings back to None for nullable columns
                if val == "":
                    val = None
                # Convert integer PKs and FKs back to int
                elif col in ("id", "flow_id", "from_tuple", "to_tuple", "git_dirty") and val is not None:
                    if table_name != "sessions" or col != "id":
                        try:
                            val = int(val)
                        except (ValueError, TypeError):
                            pass
                values.append(val)
            conn.execute(insert_sql, values)

        print(f"  Imported {len(rows):>4} rows <- {csv_path}")

    conn.commit()

    # Validate foreign key integrity
    fk_errors = conn.execute("PRAGMA foreign_key_check").fetchall()
    if fk_errors:
        print(f"\nWARNING: {len(fk_errors)} foreign key violation(s) detected:", file=sys.stderr)
        for err in fk_errors:
            print(f"  Table={err[0]} RowID={err[1]} Parent={err[2]} FK_Index={err[3]}", file=sys.stderr)
    else:
        print("Foreign key integrity: OK")

    conn.close()
    print("CSV import complete.")


def _load_csv_dir(dir_path):
    """Load all CSV tables from a directory into a dict of {table_name: [rows]}."""
    data = {}
    for table_name in TABLE_COLUMNS:
        csv_path = Path(dir_path) / f"{table_name}.csv"
        if csv_path.exists():
            data[table_name] = _read_csv_table(csv_path)
        else:
            data[table_name] = []
    return data


def cmd_csv_merge(args):
    """Merge two sets of CSV files with deterministic ID remapping.

    Strategy:
    - sessions: union by name, keep later updated_at on conflict
    - flows: union by (session_id, name), follow parent session winner
    - tuples: belong to parent flow
    - edges: kept if both endpoint tuples exist
    - findings: union by (session_id, category, description), dedup by content
    """
    ours_dir = CSV_DIR
    theirs_dir = Path(args.theirs_dir)

    if not ours_dir.exists():
        print(f"Error: Ours CSV directory not found at {ours_dir}", file=sys.stderr)
        print("Run: python audit.py csv-export", file=sys.stderr)
        sys.exit(1)

    if not theirs_dir.exists():
        print(f"Error: Theirs directory not found at {theirs_dir}", file=sys.stderr)
        sys.exit(1)

    ours = _load_csv_dir(ours_dir)
    theirs = _load_csv_dir(theirs_dir)

    # -----------------------------------------------------------------------
    # Phase 1: Merge sessions by name (unique key)
    # -----------------------------------------------------------------------
    merged_sessions = {}  # name -> row
    # Track which source won for each session name: "ours" or "theirs"
    session_winner = {}  # session_name -> "ours" | "theirs"
    # Map: (source, original_session_id) -> merged session id (TEXT, no remapping needed)
    session_id_map = {}  # (source, old_id) -> new_id (sessions use TEXT PK, kept as-is from winner)

    for row in ours.get("sessions", []):
        merged_sessions[row["name"]] = dict(row)
        session_winner[row["name"]] = "ours"

    for row in theirs.get("sessions", []):
        name = row["name"]
        if name in merged_sessions:
            # Conflict: keep later updated_at
            ours_updated = merged_sessions[name].get("updated_at", "")
            theirs_updated = row.get("updated_at", "")
            if theirs_updated > ours_updated:
                merged_sessions[name] = dict(row)
                session_winner[name] = "theirs"
        else:
            merged_sessions[name] = dict(row)
            session_winner[name] = "theirs"

    # Build session_id_map: for winning source, map old_id -> winning session id
    # We keep the winner's session id as the canonical one.
    # Build reverse lookup: session_name -> session_id (from winner)
    session_name_to_id = {}
    for row in ours.get("sessions", []):
        session_id_map[("ours", row["id"])] = row["id"]
    for row in theirs.get("sessions", []):
        session_id_map[("theirs", row["id"])] = row["id"]

    # For the final merged set, use the winner's session row (including its id)
    for name, winner in session_winner.items():
        session_name_to_id[name] = merged_sessions[name]["id"]

    # -----------------------------------------------------------------------
    # Phase 2: Merge flows by (session_id, name)
    # Flows follow their parent session's winner.
    # -----------------------------------------------------------------------

    # Build lookup: session_name by session_id for each source
    ours_sid_to_name = {r["id"]: r["name"] for r in ours.get("sessions", [])}
    theirs_sid_to_name = {r["id"]: r["name"] for r in theirs.get("sessions", [])}

    # Collect candidate flows from winning sources
    merged_flows = {}  # (session_name, flow_name) -> row
    flow_source = {}   # (session_name, flow_name) -> "ours" | "theirs"

    for row in ours.get("flows", []):
        sess_name = ours_sid_to_name.get(row["session_id"])
        if sess_name is None:
            continue
        key = (sess_name, row["name"])
        winner = session_winner.get(sess_name, "ours")
        if winner == "ours":
            merged_flows[key] = dict(row)
            flow_source[key] = "ours"
        else:
            # Session won by theirs -- ours flows are secondary
            merged_flows[key] = dict(row)
            flow_source[key] = "ours"

    for row in theirs.get("flows", []):
        sess_name = theirs_sid_to_name.get(row["session_id"])
        if sess_name is None:
            continue
        key = (sess_name, row["name"])
        winner = session_winner.get(sess_name, "theirs")
        if winner == "theirs":
            # Theirs session won -- theirs flows take precedence
            merged_flows[key] = dict(row)
            flow_source[key] = "theirs"
        elif key not in merged_flows:
            # Session won by ours but this flow only exists in theirs
            merged_flows[key] = dict(row)
            flow_source[key] = "theirs"

    # Assign new sequential flow IDs
    new_flow_id = 1
    flow_id_map = {}  # (source, old_flow_id) -> new_flow_id
    final_flows = []

    for (sess_name, flow_name) in sorted(merged_flows.keys()):
        row = merged_flows[(sess_name, flow_name)]
        source = flow_source[(sess_name, flow_name)]
        old_id = row["id"]
        flow_id_map[(source, str(old_id))] = new_flow_id

        new_row = dict(row)
        new_row["id"] = str(new_flow_id)
        new_row["session_id"] = session_name_to_id[sess_name]
        final_flows.append(new_row)
        new_flow_id += 1

    # -----------------------------------------------------------------------
    # Phase 3: Merge tuples -- belong to their parent flow
    # -----------------------------------------------------------------------
    new_tuple_id = 1
    tuple_id_map = {}  # (source, old_tuple_id_str) -> new_tuple_id
    final_tuples = []

    # Collect tuples from flows that made it into the merged set
    def _collect_tuples(source_label, source_flows, source_tuples):
        nonlocal new_tuple_id
        # Build flow_id -> (sess_name, flow_name) lookup for this source
        if source_label == "ours":
            sid_to_name = ours_sid_to_name
        else:
            sid_to_name = theirs_sid_to_name

        flow_id_to_key = {}
        for f in source_flows:
            sn = sid_to_name.get(f["session_id"])
            if sn:
                flow_id_to_key[str(f["id"])] = (sn, f["name"])

        for t in source_tuples:
            fk = flow_id_to_key.get(str(t["flow_id"]))
            if fk is None:
                continue
            # Check this flow belongs to this source in the merge
            if flow_source.get(fk) != source_label:
                continue
            old_tid = str(t["id"])
            tuple_id_map[(source_label, old_tid)] = new_tuple_id
            new_row = dict(t)
            new_row["id"] = str(new_tuple_id)
            new_row["flow_id"] = str(flow_id_map[(source_label, str(t["flow_id"]))])
            final_tuples.append(new_row)
            new_tuple_id += 1

    _collect_tuples("ours", ours.get("flows", []), ours.get("tuples", []))
    _collect_tuples("theirs", theirs.get("flows", []), theirs.get("tuples", []))

    # -----------------------------------------------------------------------
    # Phase 4: Merge edges -- kept if both endpoint tuples exist
    # -----------------------------------------------------------------------
    new_edge_id = 1
    final_edges = []

    def _collect_edges(source_label, source_edges):
        nonlocal new_edge_id
        for e in source_edges:
            from_key = (source_label, str(e["from_tuple"]))
            to_key = (source_label, str(e["to_tuple"]))
            new_from = tuple_id_map.get(from_key)
            new_to = tuple_id_map.get(to_key)
            if new_from is None or new_to is None:
                continue
            new_row = dict(e)
            new_row["id"] = str(new_edge_id)
            new_row["from_tuple"] = str(new_from)
            new_row["to_tuple"] = str(new_to)
            final_edges.append(new_row)
            new_edge_id += 1

    _collect_edges("ours", ours.get("edges", []))
    _collect_edges("theirs", theirs.get("edges", []))

    # -----------------------------------------------------------------------
    # Phase 5: Merge findings -- dedup by (session_id, category, description)
    # -----------------------------------------------------------------------
    new_finding_id = 1
    final_findings = []
    seen_findings = set()  # (session_name, category, description)

    def _collect_findings(source_label, source_findings, sid_to_name_map):
        nonlocal new_finding_id
        for f in source_findings:
            sess_name = sid_to_name_map.get(f["session_id"])
            if sess_name is None:
                continue
            dedup_key = (sess_name, f.get("category", ""), f.get("description", ""))
            if dedup_key in seen_findings:
                continue
            seen_findings.add(dedup_key)

            new_row = dict(f)
            new_row["id"] = str(new_finding_id)
            new_row["session_id"] = session_name_to_id.get(sess_name, f["session_id"])

            # Remap flow_id if present
            old_flow_id = f.get("flow_id", "")
            if old_flow_id and old_flow_id != "":
                new_fid = flow_id_map.get((source_label, str(old_flow_id)))
                new_row["flow_id"] = str(new_fid) if new_fid else ""
            else:
                new_row["flow_id"] = ""

            # Remap tuple_refs JSON array
            old_refs = f.get("tuple_refs", "[]")
            if old_refs and old_refs != "":
                try:
                    ref_list = json.loads(old_refs) if isinstance(old_refs, str) else old_refs
                    new_refs = []
                    for ref in ref_list:
                        new_ref = tuple_id_map.get((source_label, str(ref)))
                        if new_ref is not None:
                            new_refs.append(new_ref)
                    new_row["tuple_refs"] = json.dumps(new_refs)
                except (json.JSONDecodeError, TypeError):
                    new_row["tuple_refs"] = "[]"
            else:
                new_row["tuple_refs"] = "[]"

            final_findings.append(new_row)
            new_finding_id += 1

    _collect_findings("ours", ours.get("findings", []), ours_sid_to_name)
    _collect_findings("theirs", theirs.get("findings", []), theirs_sid_to_name)

    # -----------------------------------------------------------------------
    # Write merged CSV files
    # -----------------------------------------------------------------------
    CSV_DIR.mkdir(parents=True, exist_ok=True)

    merged_session_rows = sorted(merged_sessions.values(), key=lambda r: str(r.get("id", "")))
    _write_csv_table(merged_session_rows, TABLE_COLUMNS["sessions"], CSV_DIR / "sessions.csv")
    print(f"  Merged {len(merged_session_rows):>4} sessions")

    final_flows.sort(key=lambda r: int(r["id"]))
    _write_csv_table(final_flows, TABLE_COLUMNS["flows"], CSV_DIR / "flows.csv")
    print(f"  Merged {len(final_flows):>4} flows")

    final_tuples.sort(key=lambda r: int(r["id"]))
    _write_csv_table(final_tuples, TABLE_COLUMNS["tuples"], CSV_DIR / "tuples.csv")
    print(f"  Merged {len(final_tuples):>4} tuples")

    final_edges.sort(key=lambda r: int(r["id"]))
    _write_csv_table(final_edges, TABLE_COLUMNS["edges"], CSV_DIR / "edges.csv")
    print(f"  Merged {len(final_edges):>4} edges")

    final_findings.sort(key=lambda r: int(r["id"]))
    _write_csv_table(final_findings, TABLE_COLUMNS["findings"], CSV_DIR / "findings.csv")
    print(f"  Merged {len(final_findings):>4} findings")

    print("\nCSV merge complete. Run 'python audit.py csv-import' to load into database.")


# ---------------------------------------------------------------------------
# Git merge driver: db-merge %O %A %B
# ---------------------------------------------------------------------------

def _db_read_all(db_path):
    """Read all tables from a SQLite database into dict of {table: [rows]}."""
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    data = {}
    for table_name, columns in TABLE_COLUMNS.items():
        try:
            rows = conn.execute(
                f"SELECT {', '.join(columns)} FROM {table_name}"
            ).fetchall()
            data[table_name] = [dict(zip(columns, r)) for r in rows]
        except sqlite3.OperationalError:
            data[table_name] = []
    conn.close()
    return data


def _db_write_all(db_path, merged):
    """Write merged data into a fresh SQLite database."""
    if Path(db_path).exists():
        Path(db_path).unlink()
    conn = sqlite3.connect(db_path)
    conn.execute("PRAGMA foreign_keys = OFF")  # We handle integrity ourselves
    with open(SCHEMA_PATH) as f:
        conn.executescript(f.read())

    import_order = ["sessions", "flows", "tuples", "edges", "findings"]
    for table_name in import_order:
        rows = merged.get(table_name, [])
        if not rows:
            continue
        columns = TABLE_COLUMNS[table_name]
        placeholders = ", ".join(["?"] * len(columns))
        col_list = ", ".join(columns)
        sql = f"INSERT INTO {table_name} ({col_list}) VALUES ({placeholders})"
        for row in rows:
            values = []
            for col in columns:
                val = row.get(col)
                if val == "":
                    val = None
                values.append(val)
            conn.execute(sql, values)
    conn.commit()

    # Verify
    fk_errors = conn.execute("PRAGMA foreign_key_check").fetchall()
    conn.close()
    return fk_errors


def _merge_databases(ours_data, theirs_data):
    """Merge two database snapshots using session-name-based union logic.

    Returns dict of {table_name: [merged_rows]}.
    """
    # Phase 1: Sessions by name, later updated_at wins
    merged_sessions = {}
    session_winner = {}

    for row in ours_data.get("sessions", []):
        merged_sessions[row["name"]] = dict(row)
        session_winner[row["name"]] = "ours"

    for row in theirs_data.get("sessions", []):
        name = row["name"]
        if name in merged_sessions:
            ours_ts = merged_sessions[name].get("updated_at", "")
            theirs_ts = row.get("updated_at", "")
            if theirs_ts > ours_ts:
                merged_sessions[name] = dict(row)
                session_winner[name] = "theirs"
        else:
            merged_sessions[name] = dict(row)
            session_winner[name] = "theirs"

    session_name_to_id = {n: r["id"] for n, r in merged_sessions.items()}

    # Lookups: session_id -> session_name per source
    ours_sid = {r["id"]: r["name"] for r in ours_data.get("sessions", [])}
    theirs_sid = {r["id"]: r["name"] for r in theirs_data.get("sessions", [])}

    # Phase 2: Flows by (session_name, flow_name)
    merged_flows = {}
    flow_source = {}

    for row in ours_data.get("flows", []):
        sn = ours_sid.get(row["session_id"])
        if sn is None:
            continue
        key = (sn, row["name"])
        merged_flows[key] = dict(row)
        flow_source[key] = "ours"

    for row in theirs_data.get("flows", []):
        sn = theirs_sid.get(row["session_id"])
        if sn is None:
            continue
        key = (sn, row["name"])
        winner = session_winner.get(sn, "theirs")
        if winner == "theirs":
            merged_flows[key] = dict(row)
            flow_source[key] = "theirs"
        elif key not in merged_flows:
            merged_flows[key] = dict(row)
            flow_source[key] = "theirs"

    # Assign new flow IDs
    new_fid = 1
    flow_id_map = {}
    final_flows = []
    for (sn, fn) in sorted(merged_flows.keys()):
        row = merged_flows[(sn, fn)]
        src = flow_source[(sn, fn)]
        flow_id_map[(src, row["id"])] = new_fid
        new_row = dict(row)
        new_row["id"] = new_fid
        new_row["session_id"] = session_name_to_id[sn]
        final_flows.append(new_row)
        new_fid += 1

    # Phase 3: Tuples — follow parent flow
    new_tid = 1
    tuple_id_map = {}
    final_tuples = []

    def _collect_tuples(label, src_flows, src_tuples, sid_map):
        nonlocal new_tid
        fid_to_key = {}
        for f in src_flows:
            sn = sid_map.get(f["session_id"])
            if sn:
                fid_to_key[f["id"]] = (sn, f["name"])
        for t in src_tuples:
            fk = fid_to_key.get(t["flow_id"])
            if fk is None or flow_source.get(fk) != label:
                continue
            tuple_id_map[(label, t["id"])] = new_tid
            new_row = dict(t)
            new_row["id"] = new_tid
            new_row["flow_id"] = flow_id_map[(label, t["flow_id"])]
            final_tuples.append(new_row)
            new_tid += 1

    _collect_tuples("ours", ours_data.get("flows", []),
                    ours_data.get("tuples", []), ours_sid)
    _collect_tuples("theirs", theirs_data.get("flows", []),
                    theirs_data.get("tuples", []), theirs_sid)

    # Phase 4: Edges — kept if both endpoints survive
    new_eid = 1
    final_edges = []

    def _collect_edges(label, src_edges):
        nonlocal new_eid
        for e in src_edges:
            nf = tuple_id_map.get((label, e["from_tuple"]))
            nt = tuple_id_map.get((label, e["to_tuple"]))
            if nf is None or nt is None:
                continue
            new_row = dict(e)
            new_row["id"] = new_eid
            new_row["from_tuple"] = nf
            new_row["to_tuple"] = nt
            final_edges.append(new_row)
            new_eid += 1

    _collect_edges("ours", ours_data.get("edges", []))
    _collect_edges("theirs", theirs_data.get("edges", []))

    # Phase 5: Findings — dedup by (session_name, category, description)
    new_findid = 1
    final_findings = []
    seen = set()

    def _collect_findings(label, src_findings, sid_map):
        nonlocal new_findid
        for f in src_findings:
            sn = sid_map.get(f["session_id"])
            if sn is None:
                continue
            dk = (sn, f.get("category", ""), f.get("description", ""))
            if dk in seen:
                continue
            seen.add(dk)
            new_row = dict(f)
            new_row["id"] = new_findid
            new_row["session_id"] = session_name_to_id.get(sn, f["session_id"])
            # Remap flow_id
            old_fid = f.get("flow_id")
            if old_fid is not None:
                new_row["flow_id"] = flow_id_map.get((label, old_fid))
            # Remap tuple_refs
            old_refs = f.get("tuple_refs", "[]")
            if old_refs:
                try:
                    refs = json.loads(old_refs) if isinstance(old_refs, str) else (old_refs or [])
                    new_row["tuple_refs"] = json.dumps(
                        [tuple_id_map[(label, r)] for r in refs
                         if (label, r) in tuple_id_map]
                    )
                except (json.JSONDecodeError, TypeError):
                    new_row["tuple_refs"] = "[]"
            final_findings.append(new_row)
            new_findid += 1

    _collect_findings("ours", ours_data.get("findings", []), ours_sid)
    _collect_findings("theirs", theirs_data.get("findings", []), theirs_sid)

    return {
        "sessions": sorted(merged_sessions.values(), key=lambda r: str(r.get("id", ""))),
        "flows": sorted(final_flows, key=lambda r: r["id"]),
        "tuples": sorted(final_tuples, key=lambda r: r["id"]),
        "edges": sorted(final_edges, key=lambda r: r["id"]),
        "findings": sorted(final_findings, key=lambda r: r["id"]),
    }


def cmd_db_merge(args):
    """Git merge driver: merge two audit.db files.

    Called by git as: audit.py db-merge %O %A %B
      %O = ancestor (unused — we do full union, not 3-way)
      %A = ours (result written here)
      %B = theirs
    Exit 0 = success, 1 = conflict.
    """
    ours_path = args.ours
    theirs_path = args.theirs

    if not Path(ours_path).exists():
        print(f"Error: ours DB not found: {ours_path}", file=sys.stderr)
        sys.exit(1)
    if not Path(theirs_path).exists():
        print(f"Error: theirs DB not found: {theirs_path}", file=sys.stderr)
        sys.exit(1)

    print(f"Merging audit databases...")
    print(f"  Ours:   {ours_path}")
    print(f"  Theirs: {theirs_path}")

    ours_data = _db_read_all(ours_path)
    theirs_data = _db_read_all(theirs_path)

    merged = _merge_databases(ours_data, theirs_data)

    # Write merged result to ours path (git expects result in %A)
    fk_errors = _db_write_all(ours_path, merged)

    for table_name in TABLE_COLUMNS:
        print(f"  {table_name}: {len(merged.get(table_name, []))} rows")

    if fk_errors:
        print(f"\nWARNING: {len(fk_errors)} FK violations — merge may need manual review",
              file=sys.stderr)
        sys.exit(1)

    print("Merge complete.")
    sys.exit(0)


def cmd_db_dump(args):
    """Dump SQLite database as SQL text. Used as git textconv driver."""
    db_path = args.db_path
    if not Path(db_path).exists():
        print(f"-- Empty database: {db_path}", file=sys.stderr)
        sys.exit(0)
    conn = sqlite3.connect(db_path)
    for line in conn.iterdump():
        print(line)
    conn.close()


def cmd_git_setup(args):
    """Configure git merge and diff drivers for audit.db."""

    # Find git repo root
    try:
        repo_root = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True
        ).stdout.strip()
    except subprocess.CalledProcessError:
        print("Error: not in a git repository", file=sys.stderr)
        sys.exit(1)

    # Resolve the audit.py path relative to repo root
    script_path = Path(__file__).resolve()
    repo_path = Path(repo_root).resolve()
    try:
        rel_script = script_path.relative_to(repo_path)
    except ValueError:
        rel_script = script_path
    script_ref = str(rel_script)

    # Configure merge driver
    subprocess.run([
        "git", "config", "merge.sqlite-audit.name",
        "SQLite audit database merge"
    ], check=True)
    subprocess.run([
        "git", "config", "merge.sqlite-audit.driver",
        f"python3 {script_ref} db-merge %O %A %B"
    ], check=True)

    # Configure diff driver (uses db-dump for textconv)
    subprocess.run([
        "git", "config", "diff.sqlite.textconv",
        f"python3 {script_ref} db-dump"
    ], check=True)

    print("Git drivers configured:")
    print(f"  merge.sqlite-audit.driver = python {script_ref} db-merge %O %A %B")
    print(f"  diff.sqlite.textconv = python {script_ref} db-dump")
    print()

    # Check .gitattributes
    ga_path = Path(repo_root) / ".gitattributes"
    ga_line = ".audit/audit.db diff=sqlite merge=sqlite-audit"
    if ga_path.exists():
        content = ga_path.read_text()
        if ga_line in content:
            print(f".gitattributes already has audit.db entry")
        else:
            print(f"Add this line to .gitattributes:\n  {ga_line}")
    else:
        print(f"Add this line to .gitattributes:\n  {ga_line}")

    print("\nDone! Run 'git diff .audit/audit.db' to test SQL diff output.")


def main():
    parser = argparse.ArgumentParser(
        description="Audit Flow CLI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # init
    init_parser = subparsers.add_parser("init", help="Initialize database")
    init_parser.add_argument("--force", action="store_true", help="Reinitialize")

    # list
    subparsers.add_parser("list", help="List all sessions")

    # show
    show_parser = subparsers.add_parser("show", help="Show session/flow details")
    show_parser.add_argument("session", help="Session name or ID")
    show_parser.add_argument("flow", nargs="?", help="Flow name (optional)")

    # export
    export_parser = subparsers.add_parser("export", help="Export session/flow")
    export_parser.add_argument("session", help="Session name or ID")
    export_parser.add_argument("--flow", "-f", help="Flow name (exports all flows if omitted)")
    export_parser.add_argument("--direction", "-d", default="TD",
                              choices=["TD", "LR"],
                              help="Mermaid flowchart direction (default: TD)")
    export_parser.add_argument("--format", "-F", default="all",
                              choices=["json", "yaml", "md", "markdown", "mermaid", "all"],
                              help="Export format (default: all)")

    # validate
    validate_parser = subparsers.add_parser("validate", help="Validate session flows")
    validate_parser.add_argument("session", help="Session name or ID")

    # csv-export
    subparsers.add_parser("csv-export", help="Export all tables to CSV in .audit/csv/")

    # csv-import
    subparsers.add_parser("csv-import", help="Import CSV files from .audit/csv/ into database")

    # csv-merge
    merge_parser = subparsers.add_parser("csv-merge", help="Merge theirs CSV files into ours")
    merge_parser.add_argument("theirs_dir", help="Directory containing theirs CSV files")

    # db-merge (git merge driver: %O %A %B)
    db_merge_parser = subparsers.add_parser("db-merge",
        help="Git merge driver for audit.db (called automatically by git)")
    db_merge_parser.add_argument("ancestor", help="Common ancestor DB (%O)")
    db_merge_parser.add_argument("ours", help="Our DB (%A) — result written here")
    db_merge_parser.add_argument("theirs", help="Their DB (%B)")

    # db-dump (git textconv driver)
    db_dump_parser = subparsers.add_parser("db-dump",
        help="Dump SQLite DB as SQL text (used by git diff textconv)")
    db_dump_parser.add_argument("db_path", help="Path to SQLite database file")

    # git-setup (configure merge + diff drivers)
    subparsers.add_parser("git-setup", help="Configure git merge/diff drivers for audit.db")

    args = parser.parse_args()

    if args.command == "init":
        cmd_init(args)
    elif args.command == "list":
        cmd_list(args)
    elif args.command == "show":
        cmd_show(args)
    elif args.command == "export":
        cmd_export(args)
    elif args.command == "validate":
        cmd_validate(args)
    elif args.command == "csv-export":
        cmd_csv_export(args)
    elif args.command == "csv-import":
        cmd_csv_import(args)
    elif args.command == "csv-merge":
        cmd_csv_merge(args)
    elif args.command == "db-merge":
        cmd_db_merge(args)
    elif args.command == "db-dump":
        cmd_db_dump(args)
    elif args.command == "git-setup":
        cmd_git_setup(args)


if __name__ == "__main__":
    main()
