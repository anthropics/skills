-- Audit Flow SQLite Schema
-- Initialize: sqlite3 .audit/audit.db < .claude/skills/audit-flow/schema.sql

PRAGMA foreign_keys = ON;

-- Sessions table (audit session container)
CREATE TABLE IF NOT EXISTS sessions (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL UNIQUE,
    purpose TEXT NOT NULL CHECK (purpose IN ('security-audit', 'documentation', 'compliance', 'ideation', 'brainstorming', 'debugging', 'architecture-review', 'incident-review')),
    description TEXT,
    granularity TEXT NOT NULL CHECK (granularity IN ('fine', 'coarse')),
    -- Git context at audit start
    git_commit TEXT,
    git_branch TEXT,
    git_dirty INTEGER DEFAULT 0,  -- 0 = clean, 1 = dirty
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    updated_at TEXT NOT NULL DEFAULT (datetime('now')),
    status TEXT NOT NULL DEFAULT 'active' CHECK (status IN ('active', 'completed', 'archived'))
);

-- Flows table (named DAGs within a session)
CREATE TABLE IF NOT EXISTS flows (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
    name TEXT NOT NULL,
    entry_point TEXT NOT NULL,
    description TEXT,
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    status TEXT NOT NULL DEFAULT 'active' CHECK (status IN ('active', 'completed')),
    UNIQUE(session_id, name)
);

CREATE INDEX IF NOT EXISTS idx_flows_session ON flows(session_id);

-- Tuples table (flow steps/nodes)
CREATE TABLE IF NOT EXISTS tuples (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    flow_id INTEGER NOT NULL REFERENCES flows(id) ON DELETE CASCADE,
    timestamp TEXT NOT NULL DEFAULT (datetime('now')),
    layer TEXT NOT NULL CHECK (layer IN ('CODE', 'API', 'NETWORK', 'AUTH', 'DATA')),
    action TEXT NOT NULL,
    subject TEXT NOT NULL,
    file_ref TEXT,
    props TEXT DEFAULT '{}',  -- JSON
    notes TEXT,
    status TEXT NOT NULL DEFAULT 'traced' CHECK (status IN ('traced', 'verified', 'concern', 'deleted'))
);

CREATE INDEX IF NOT EXISTS idx_tuples_flow ON tuples(flow_id);
CREATE INDEX IF NOT EXISTS idx_tuples_layer ON tuples(layer);
CREATE INDEX IF NOT EXISTS idx_tuples_status ON tuples(status);

-- Edges table (relationships between tuples - supports non-linear flows)
CREATE TABLE IF NOT EXISTS edges (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    from_tuple INTEGER NOT NULL REFERENCES tuples(id) ON DELETE CASCADE,
    to_tuple INTEGER NOT NULL REFERENCES tuples(id) ON DELETE CASCADE,
    relation TEXT NOT NULL CHECK (relation IN ('TRIGGERS', 'READS', 'WRITES', 'VALIDATES', 'TRANSFORMS', 'BRANCHES', 'MERGES')),
    condition TEXT,  -- For conditional branches: "if authenticated", "on error"
    props TEXT DEFAULT '{}',  -- JSON
    created_at TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_edges_from ON edges(from_tuple);
CREATE INDEX IF NOT EXISTS idx_edges_to ON edges(to_tuple);

-- Findings table (security/compliance issues)
CREATE TABLE IF NOT EXISTS findings (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    session_id TEXT NOT NULL REFERENCES sessions(id) ON DELETE CASCADE,
    flow_id INTEGER REFERENCES flows(id) ON DELETE SET NULL,  -- Optional: finding can be flow-specific or session-wide
    severity TEXT NOT NULL CHECK (severity IN ('critical', 'high', 'medium', 'low', 'info')),
    category TEXT NOT NULL,
    description TEXT NOT NULL,
    tuple_refs TEXT DEFAULT '[]',  -- JSON array of tuple IDs
    status TEXT NOT NULL DEFAULT 'open' CHECK (status IN ('open', 'acknowledged', 'resolved', 'wontfix')),
    created_at TEXT NOT NULL DEFAULT (datetime('now')),
    updated_at TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_findings_session ON findings(session_id);
CREATE INDEX IF NOT EXISTS idx_findings_flow ON findings(flow_id);
CREATE INDEX IF NOT EXISTS idx_findings_severity ON findings(severity);

-- Triggers for timestamps
CREATE TRIGGER IF NOT EXISTS update_session_timestamp
AFTER UPDATE ON sessions
BEGIN
    UPDATE sessions SET updated_at = datetime('now') WHERE id = NEW.id;
END;

CREATE TRIGGER IF NOT EXISTS update_finding_timestamp
AFTER UPDATE ON findings
BEGIN
    UPDATE findings SET updated_at = datetime('now') WHERE id = NEW.id;
END;

-- ============================================================================
-- Views
-- ============================================================================

-- Session summary with flow counts
CREATE VIEW IF NOT EXISTS v_session_summary AS
SELECT
    s.id,
    s.name,
    s.purpose,
    s.status,
    s.git_commit,
    s.git_branch,
    s.git_dirty,
    s.created_at,
    COUNT(DISTINCT f.id) as flow_count,
    COUNT(DISTINCT t.id) as tuple_count,
    COUNT(DISTINCT e.id) as edge_count,
    COUNT(DISTINCT fi.id) as finding_count,
    SUM(CASE WHEN fi.severity = 'critical' THEN 1 ELSE 0 END) as critical_findings,
    SUM(CASE WHEN fi.severity = 'high' THEN 1 ELSE 0 END) as high_findings
FROM sessions s
LEFT JOIN flows f ON s.id = f.session_id
LEFT JOIN tuples t ON f.id = t.flow_id AND t.status != 'deleted'
LEFT JOIN edges e ON e.from_tuple = t.id
LEFT JOIN findings fi ON s.id = fi.session_id
GROUP BY s.id;

-- Flow summary
CREATE VIEW IF NOT EXISTS v_flow_summary AS
SELECT
    f.id,
    f.session_id,
    f.name,
    f.entry_point,
    f.status,
    f.created_at,
    s.name as session_name,
    COUNT(DISTINCT t.id) as tuple_count,
    COUNT(DISTINCT e.id) as edge_count,
    SUM(CASE WHEN t.status = 'concern' THEN 1 ELSE 0 END) as concern_count
FROM flows f
JOIN sessions s ON f.session_id = s.id
LEFT JOIN tuples t ON f.id = t.flow_id AND t.status != 'deleted'
LEFT JOIN edges e ON e.from_tuple = t.id
GROUP BY f.id;

-- Layer distribution per flow
CREATE VIEW IF NOT EXISTS v_layer_distribution AS
SELECT
    f.session_id,
    t.flow_id,
    f.name as flow_name,
    t.layer,
    COUNT(*) as count
FROM tuples t
JOIN flows f ON t.flow_id = f.id
WHERE t.status != 'deleted'
GROUP BY t.flow_id, t.layer;

-- Concerns requiring attention
CREATE VIEW IF NOT EXISTS v_concerns AS
SELECT
    t.*,
    f.name as flow_name,
    s.name as session_name
FROM tuples t
JOIN flows f ON t.flow_id = f.id
JOIN sessions s ON f.session_id = s.id
WHERE t.status = 'concern'
ORDER BY t.timestamp DESC;

-- Non-linear flow detection (nodes with multiple incoming or outgoing edges)
CREATE VIEW IF NOT EXISTS v_branch_merge_points AS
SELECT
    t.id as tuple_id,
    t.action,
    f.name as flow_name,
    COUNT(DISTINCT e_out.id) as outgoing_edges,
    COUNT(DISTINCT e_in.id) as incoming_edges,
    CASE
        WHEN COUNT(DISTINCT e_out.id) > 1 THEN 'branch'
        WHEN COUNT(DISTINCT e_in.id) > 1 THEN 'merge'
        ELSE 'linear'
    END as node_type
FROM tuples t
JOIN flows f ON t.flow_id = f.id
LEFT JOIN edges e_out ON t.id = e_out.from_tuple
LEFT JOIN edges e_in ON t.id = e_in.to_tuple
WHERE t.status != 'deleted'
GROUP BY t.id
HAVING outgoing_edges > 1 OR incoming_edges > 1;
