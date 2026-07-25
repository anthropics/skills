#!/usr/bin/env python3
"""只读数据库证据挖掘工具。

脚本负责确定性采集：配置候选、连接测试、schema、轻量画像、弱关系候选和证据包骨架。
业务解释、关键表逐字段判断和最终落档由 Agent 结合代码证据完成。
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import sqlite3
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from urllib.parse import unquote, urlparse


SKIP_DIRS = {
    ".git",
    ".idea",
    ".vscode",
    "node_modules",
    "target",
    "build",
    "dist",
    "out",
    ".gradle",
    ".mvn",
    ".venv",
    "venv",
    "__pycache__",
}

CONFIG_SUFFIXES = {
    ".env",
    ".properties",
    ".yml",
    ".yaml",
    ".json",
    ".toml",
    ".xml",
    ".ini",
    ".conf",
    ".config",
    ".cs",
    ".java",
    ".kt",
    ".js",
    ".ts",
    ".py",
    ".go",
}

CONNECTION_RE = re.compile(
    r"(?P<url>"
    r"(?:jdbc:)?(?:postgresql|postgres|mysql|mariadb|sqlite|sqlserver|mssql|oracle|kingbase8?|kingbasees)"
    r"://[^\s\"'<>]+"
    r"|jdbc:(?:postgresql|mysql|mariadb|sqlserver|oracle|kingbase8?|kingbasees):[^\s\"'<>]+"
    r"|Data Source\s*=\s*[^;\"'\n]+(?:;[^\"'\n]+)*)",
    re.IGNORECASE,
)

KEY_RE = re.compile(
    r"^\s*(?P<key>[A-Za-z0-9_.:\-]*(?:database|datasource|jdbc|connection|string|url|host|port|db|username|password)[\w.\-:]*)"
    r"\s*[:=]\s*"
    r"(?P<value>[^\n#]+)",
    re.IGNORECASE | re.MULTILINE,
)

SENSITIVE_KEY_RE = re.compile(
    r"password|passwd|pwd|secret|token|key|credential|cookie|session",
    re.IGNORECASE,
)

SENSITIVE_VALUE_RE = re.compile(
    r"(\b1[3-9]\d{9}\b)|([A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,})|([A-Za-z0-9_\-]{24,})"
)


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def write_json(data: Any, output: Optional[str]) -> None:
    text = json.dumps(data, ensure_ascii=False, indent=2, default=str)
    if output:
        Path(output).write_text(text + "\n", encoding="utf-8")
    else:
        print(text)


def read_json(path: str) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def mask_secret(value: str) -> str:
    value = value.strip().strip("\"'")
    value = re.sub(r"(?i)(password|passwd|pwd|secret|token|key)=([^;&\s]+)", r"\1=***", value)
    value = re.sub(r"(?i)(://[^:/@\s]+):([^@\s]+)@", r"\1:***@", value)
    value = re.sub(r"(?i)(User ID|UID|User|Username|userId)=([^;\"'\s]+)", r"\1=***", value)
    value = re.sub(r"(?i)(Password|PWD)=([^;]+)", r"\1=***", value)
    return value


def clean_config_value(value: str) -> str:
    value = value.strip().strip(",")
    if value.startswith(("\"", "'")):
        quote = value[0]
        end = value.find(quote, 1)
        if end > 0:
            return value[1:end]
    if "\"" in value:
        value = value.split("\"", 1)[0]
    if "'" in value:
        value = value.split("'", 1)[0]
    return value.strip()


def maybe_mask_secret(value: str, enabled: bool) -> str:
    return mask_secret(value) if enabled else value


def mask_sample(value: Any, key_hint: str = "") -> Any:
    if value is None:
        return None
    if SENSITIVE_KEY_RE.search(key_hint):
        return "***"
    if not isinstance(value, str):
        return value
    value = value.strip()
    if len(value) > 80:
        return value[:80] + "...(truncated)"
    return SENSITIVE_VALUE_RE.sub("***", value)


def maybe_mask_sample(value: Any, key_hint: str, enabled: bool) -> Any:
    if enabled:
        return mask_sample(value, key_hint)
    if isinstance(value, str) and len(value) > 200:
        return value[:200] + "...(truncated)"
    return value


def iter_candidate_files(root: Path, max_file_bytes: int) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS and not d.startswith(".cache")]
        for filename in filenames:
            path = Path(dirpath) / filename
            lower = filename.lower()
            if not (path.suffix.lower() in CONFIG_SUFFIXES or lower.startswith(".env") or "config" in lower):
                continue
            try:
                if path.stat().st_size > max_file_bytes:
                    continue
            except OSError:
                continue
            yield path


def db_type_hint(value: str) -> str:
    lower = value.lower()
    for name in ["postgresql", "postgres", "mysql", "mariadb", "sqlite", "sqlserver", "mssql", "oracle", "kingbase", "kingbase8", "kingbasees"]:
        if name in lower:
            if name == "postgres":
                return "postgresql"
            if name in {"kingbase", "kingbase8", "kingbasees"}:
                return "kingbase"
            return name
    return "unknown"


def is_source_file(path: Path) -> bool:
    return path.suffix.lower() in {".java", ".kt", ".cs", ".js", ".ts", ".py", ".go"}


def is_db_config_key(key: str) -> bool:
    lower = key.lower()
    strong_tokens = [
        "db.url",
        "db.jdbcurl",
        "db.slavejdbcurl",
        "jdbc.url",
        "jdbcurl",
        "datasource.url",
        "spring.datasource.url",
        "connectionstring",
        "connectionurl",
        "connectionstrings",
        "database.type",
        "db.username",
        "db.user",
        "db.password",
        "db.slaveusername",
        "db.slavepassword",
        "datasource.username",
        "datasource.user",
        "datasource.password",
        "dataSource.quartzDS.URL".lower(),
        "dataSource.quartzDS.driver".lower(),
        "dataSource.quartzDS.user".lower(),
        "dataSource.quartzDS.password".lower(),
    ]
    return any(token in lower for token in strong_tokens) or (
        ("database" in lower or "datasource" in lower or "jdbc" in lower) and any(x in lower for x in ["url", "driver", "type"])
    )


def discover_config(args: argparse.Namespace) -> None:
    root = Path(args.root).resolve()
    findings: List[Dict[str, Any]] = []
    for path in iter_candidate_files(root, args.max_file_bytes):
        try:
            text = path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        rel = str(path.relative_to(root))
        for match in CONNECTION_RE.finditer(text):
            raw = clean_config_value(match.group("url"))
            findings.append(
                {
                    "source_file": rel,
                    "source_key": "connection_string",
                    "db_type_hint": db_type_hint(raw),
                    "value": maybe_mask_secret(raw, args.mask_sensitive),
                    "confidence": "high",
                    "notes": [],
                }
            )
        if is_source_file(path):
            continue
        for match in KEY_RE.finditer(text):
            key = match.group("key").strip()
            value = clean_config_value(match.group("value"))
            if not value or len(value) > 300:
                continue
            key_lower = key.lower()
            sensitive_db_key = bool(SENSITIVE_KEY_RE.search(key)) and any(
                token in key_lower for token in ["db", "database", "datasource", "jdbc", "connection"]
            )
            interesting = sensitive_db_key or is_db_config_key(key) or CONNECTION_RE.search(value)
            if not interesting:
                continue
            findings.append(
                {
                    "source_file": rel,
                    "source_key": key,
                    "db_type_hint": db_type_hint(value),
                    "value": maybe_mask_secret(value, args.mask_sensitive),
                    "confidence": "medium",
                    "notes": ["配置片段候选，需结合运行环境、启动参数或配置覆盖关系判断是否生效"],
                }
            )
    deduped = []
    seen = set()
    for item in findings:
        key = (item["source_file"], item["source_key"], item["value"])
        if key in seen:
            continue
        seen.add(key)
        deduped.append(item)
    write_json({"root": str(root), "connection_candidates": deduped}, args.output)


def normalize_sqlite_path(url: str) -> Optional[str]:
    if url.startswith("sqlite:///"):
        return url[len("sqlite:///") :]
    if url.startswith("sqlite://"):
        parsed = urlparse(url)
        return parsed.path
    if url.endswith(".db") or url.endswith(".sqlite") or url.endswith(".sqlite3"):
        return url
    return None


def is_postgres_like_url(url: str) -> bool:
    return urlparse(url).scheme.startswith("postgresql")


def psycopg2_connect(url: str):
    try:
        import psycopg2
    except Exception as exc:  # pragma: no cover
        raise RuntimeError("缺少 psycopg2，无法使用 PostgreSQL-like fallback") from exc
    parsed = urlparse(url)
    return psycopg2.connect(
        host=parsed.hostname,
        port=parsed.port or 5432,
        dbname=(parsed.path or "/").lstrip("/"),
        user=unquote(parsed.username or ""),
        password=unquote(parsed.password or ""),
        connect_timeout=5,
    )


def pg_quote_ident(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def pg_database_type(version: str) -> str:
    return "kingbase" if "kingbase" in version.lower() else "postgresql"


def get_sqlalchemy_engine(url: str):
    try:
        from sqlalchemy import create_engine
    except Exception as exc:  # pragma: no cover - depends on optional package
        raise RuntimeError("缺少 SQLAlchemy。可安装到本地环境后重试：python3 -m pip install sqlalchemy") from exc
    return create_engine(url)


def test_connection(args: argparse.Namespace) -> None:
    sqlite_path = normalize_sqlite_path(args.url)
    if sqlite_path:
        con = sqlite3.connect(sqlite_path)
        try:
            row = con.execute("select 1").fetchone()
        finally:
            con.close()
        write_json({"ok": row == (1,), "database_type": "sqlite", "url": maybe_mask_secret(args.url, args.mask_sensitive)}, args.output)
        return
    try:
        try:
            engine = get_sqlalchemy_engine(args.url)
            with engine.connect() as con:
                row = con.exec_driver_sql("select 1").fetchone()
            ok = bool(row and row[0] == 1)
            db_type = engine.dialect.name
        finally:
            if "engine" in locals():
                engine.dispose()
    except Exception:
        if not is_postgres_like_url(args.url):
            raise
        con = psycopg2_connect(args.url)
        try:
            cur = con.cursor()
            cur.execute("select version()")
            version = cur.fetchone()[0]
            cur.execute("select 1")
            ok = cur.fetchone() == (1,)
            db_type = pg_database_type(version)
        finally:
            con.close()
    write_json({"ok": ok, "database_type": db_type, "url": maybe_mask_secret(args.url, args.mask_sensitive)}, args.output)


def sqlite_introspect(url: str) -> Dict[str, Any]:
    sqlite_path = normalize_sqlite_path(url)
    if not sqlite_path:
        raise ValueError("不是 SQLite URL")
    con = sqlite3.connect(sqlite_path)
    con.row_factory = sqlite3.Row
    try:
        tables = []
        table_rows = con.execute(
            "select name, type, sql from sqlite_master where type in ('table','view') and name not like 'sqlite_%' order by name"
        ).fetchall()
        for row in table_rows:
            name = row["name"]
            columns = []
            for col in con.execute(f'pragma table_info("{name}")').fetchall():
                columns.append(
                    {
                        "name": col["name"],
                        "type": col["type"],
                        "nullable": not bool(col["notnull"]),
                        "default": col["dflt_value"],
                        "primary_key": bool(col["pk"]),
                        "comment": None,
                    }
                )
            indexes = []
            for idx in con.execute(f'pragma index_list("{name}")').fetchall():
                idx_name = idx["name"]
                idx_cols = [c["name"] for c in con.execute(f'pragma index_info("{idx_name}")').fetchall()]
                indexes.append({"name": idx_name, "unique": bool(idx["unique"]), "columns": idx_cols})
            fks = []
            for fk in con.execute(f'pragma foreign_key_list("{name}")').fetchall():
                fks.append(
                    {
                        "columns": [fk["from"]],
                        "referred_table": fk["table"],
                        "referred_columns": [fk["to"]],
                    }
                )
            tables.append(
                {
                    "schema": "main",
                    "name": name,
                    "type": row["type"],
                    "columns": columns,
                    "primary_key": [c["name"] for c in columns if c["primary_key"]],
                    "indexes": indexes,
                    "foreign_keys": fks,
                    "comment": None,
                }
            )
        return {"metadata": {"generated_at": utc_now(), "database_type": "sqlite"}, "tables": tables}
    finally:
        con.close()


def sqlalchemy_introspect(url: str) -> Dict[str, Any]:
    try:
        from sqlalchemy import inspect
    except Exception as exc:  # pragma: no cover
        raise RuntimeError("缺少 SQLAlchemy。可安装到本地环境后重试：python3 -m pip install sqlalchemy") from exc
    engine = get_sqlalchemy_engine(url)
    inspector = inspect(engine)
    try:
        schemas = args_schemas = None
        try:
            schemas = inspector.get_schema_names()
        except Exception:
            schemas = [None]
        tables = []
        for schema in schemas or [None]:
            if schema in {"information_schema", "pg_catalog"}:
                continue
            for table_name in inspector.get_table_names(schema=schema):
                columns = []
                for col in inspector.get_columns(table_name, schema=schema):
                    columns.append(
                        {
                            "name": col.get("name"),
                            "type": str(col.get("type")),
                            "nullable": col.get("nullable"),
                            "default": str(col.get("default")) if col.get("default") is not None else None,
                            "primary_key": False,
                            "comment": col.get("comment"),
                        }
                    )
                pk = inspector.get_pk_constraint(table_name, schema=schema).get("constrained_columns") or []
                for col in columns:
                    col["primary_key"] = col["name"] in pk
                tables.append(
                    {
                        "schema": schema,
                        "name": table_name,
                        "type": "table",
                        "columns": columns,
                        "primary_key": pk,
                        "indexes": inspector.get_indexes(table_name, schema=schema),
                        "foreign_keys": inspector.get_foreign_keys(table_name, schema=schema),
                        "comment": (inspector.get_table_comment(table_name, schema=schema) or {}).get("text"),
                    }
                )
        return {"metadata": {"generated_at": utc_now(), "database_type": engine.dialect.name}, "tables": tables}
    finally:
        engine.dispose()


def postgres_like_introspect(url: str) -> Dict[str, Any]:
    con = psycopg2_connect(url)
    try:
        cur = con.cursor()
        cur.execute("select version()")
        version = cur.fetchone()[0]
        cur.execute(
            """
            select table_schema, table_name, table_type
            from information_schema.tables
            where table_schema not in ('information_schema', 'pg_catalog', 'sys_catalog')
              and table_schema not like 'pg_%'
              and table_type in ('BASE TABLE', 'VIEW')
            order by table_schema, table_name
            """
        )
        rows = cur.fetchall()
        tables = []
        for schema_name, table_name, table_type in rows:
            cur.execute(
                """
                select column_name, data_type, udt_name, is_nullable, column_default
                from information_schema.columns
                where table_schema = %s and table_name = %s
                order by ordinal_position
                """,
                (schema_name, table_name),
            )
            column_rows = cur.fetchall()
            cur.execute(
                """
                select kcu.column_name
                from information_schema.table_constraints tc
                join information_schema.key_column_usage kcu
                  on tc.constraint_name = kcu.constraint_name
                 and tc.table_schema = kcu.table_schema
                 and tc.table_name = kcu.table_name
                where tc.constraint_type = 'PRIMARY KEY'
                  and tc.table_schema = %s
                  and tc.table_name = %s
                order by kcu.ordinal_position
                """,
                (schema_name, table_name),
            )
            pk = [r[0] for r in cur.fetchall()]
            columns = [
                {
                    "name": name,
                    "type": udt_name or data_type,
                    "nullable": is_nullable == "YES",
                    "default": default,
                    "primary_key": name in pk,
                    "comment": None,
                }
                for name, data_type, udt_name, is_nullable, default in column_rows
            ]
            tables.append(
                {
                    "schema": schema_name,
                    "name": table_name,
                    "type": table_type.lower(),
                    "columns": columns,
                    "primary_key": pk,
                    "indexes": [],
                    "foreign_keys": [],
                    "comment": None,
                }
            )
        return {"metadata": {"generated_at": utc_now(), "database_type": pg_database_type(version)}, "tables": tables}
    finally:
        con.close()


def introspect(args: argparse.Namespace) -> None:
    if normalize_sqlite_path(args.url):
        data = sqlite_introspect(args.url)
    else:
        try:
            data = sqlalchemy_introspect(args.url)
        except Exception:
            if not is_postgres_like_url(args.url):
                raise
            data = postgres_like_introspect(args.url)
    data["metadata"]["scan_level"] = "catalog"
    data["metadata"]["connection_source"] = maybe_mask_secret(args.url, args.mask_sensitive)
    write_json(data, args.output)


def selected_tables(schema: Dict[str, Any], table_csv: Optional[str], max_tables: int) -> List[Dict[str, Any]]:
    tables = schema.get("tables", [])
    if table_csv:
        wanted = {x.strip() for x in table_csv.split(",") if x.strip()}
        tables = [t for t in tables if t.get("name") in wanted or f"{t.get('schema')}.{t.get('name')}" in wanted]
    return tables[:max_tables]


def table_full_name(table: Dict[str, Any]) -> str:
    return f"{table.get('schema')}.{table.get('name')}" if table.get("schema") else table.get("name")


def find_table(schema: Dict[str, Any], name: str) -> Dict[str, Any]:
    for table in schema.get("tables", []):
        if table.get("name") == name or table_full_name(table) == name:
            return table
    raise ValueError(f"未在 catalog 中找到表：{name}")


def table_tokens(name: str) -> List[str]:
    return [x for x in re.split(r"[_\W]+", name.lower()) if x]


def likely_system_table(table: Dict[str, Any]) -> bool:
    schema = (table.get("schema") or "").lower()
    name = (table.get("name") or "").lower()
    if schema in {"information_schema", "pg_catalog", "sys_catalog", "sys", "anon", "sys_hm", "sysmac", "src_restrict", "sysaudit"}:
        return True
    system_prefixes = (
        "dba_",
        "all_",
        "user_tab",
        "user_col",
        "user_cons",
        "user_ind",
        "user_indexes",
        "user_objects",
        "user_sequences",
        "user_source",
        "user_synonyms",
        "user_role",
        "user_free",
        "user_db",
        "user_directories",
        "user_part",
        "sys_stat_",
        "v$",
    )
    return name.startswith(system_prefixes)


def classify_catalog(args: argparse.Namespace) -> None:
    catalog = read_json(args.catalog)
    groups: Dict[str, List[str]] = {}
    guide_candidates = []
    for table in catalog.get("tables", []):
        if likely_system_table(table):
            continue
        name = table.get("name", "")
        tokens = table_tokens(name)
        key = tokens[0] if tokens else name.lower()
        groups.setdefault(key, []).append(table_full_name(table))
        lowered = name.lower()
        if any(x in lowered for x in ["config", "dict", "dictionary", "setting"]):
            guide_candidates.append({"table": table_full_name(table), "topic": "CONFIG_OR_DICTIONARY", "reason": "表名像配置/字典表"})
        if any(x in lowered for x in ["flow", "workflow", "task", "job"]):
            guide_candidates.append({"table": table_full_name(table), "topic": "FLOW_OR_TASK", "reason": "表名像流程/任务表"})
        if any(x in lowered for x in ["log", "history", "record"]):
            guide_candidates.append({"table": table_full_name(table), "topic": "HISTORY_OR_LOG", "reason": "表名像历史/日志表，通常不作为领域主表"})
    domain_hints = [
        {"hint": key, "tables": value[:50], "table_count": len(value)}
        for key, value in sorted(groups.items(), key=lambda item: len(item[1]), reverse=True)
    ]
    write_json(
        {
            "metadata": {"generated_at": utc_now(), "scan_level": "catalog-classification"},
            "domain_hints": domain_hints,
            "guide_candidates": guide_candidates,
            "note": "基于表名/字段名的轻量候选，供 Agent 结合代码和业务语义判断",
        },
        args.output,
    )


def plan_domain_scan(args: argparse.Namespace) -> None:
    catalog = read_json(args.catalog)
    keywords = [x.strip().lower() for x in (args.keywords or args.domain or "").split(",") if x.strip()]
    if args.domain and args.domain.lower() not in keywords:
        keywords.append(args.domain.lower())
    tables = []
    for table in catalog.get("tables", []):
        if likely_system_table(table):
            continue
        haystack = " ".join(
            [table.get("name", ""), table.get("comment") or ""]
            + [col.get("name", "") + " " + str(col.get("comment") or "") for col in table.get("columns", [])]
        ).lower()
        score = sum(1 for keyword in keywords if keyword and keyword in haystack)
        risk_columns = [
            col.get("name")
            for col in table.get("columns", [])
            if re.search(r"status|type|amount|balance|point|score|stock|tenant|shop|store|expire|valid|delete|shard|version|level|grade", col.get("name", ""), re.I)
        ]
        if score or risk_columns:
            tables.append(
                {
                    "table": table_full_name(table),
                    "match_score": score,
                    "risk_columns": risk_columns,
                    "suggested_next_step": "sample-table" if score else "catalog-only-until-domain-confirmed",
                }
            )
    tables.sort(key=lambda item: (item["match_score"], len(item["risk_columns"])), reverse=True)
    write_json(
        {
            "metadata": {"generated_at": utc_now(), "scan_level": "domain-scan-plan"},
            "domain": args.domain,
            "keywords": keywords,
            "tables": tables[: args.max_tables],
            "note": "这是领域细扫计划，不代表已经完成表/字段深挖",
        },
        args.output,
    )


def summarize_sample(table: Dict[str, Any], rows: List[Dict[str, Any]], args: argparse.Namespace) -> Dict[str, Any]:
    columns = []
    for col in table.get("columns", [])[: args.max_columns]:
        name = col["name"]
        values = [row.get(name) for row in rows]
        non_null = [v for v in values if v is not None]
        counts: Dict[str, int] = {}
        for value in non_null:
            key = json.dumps(maybe_mask_sample(value, name, args.mask_sensitive), ensure_ascii=False, default=str)
            counts[key] = counts.get(key, 0) + 1
        sample_values = [
            {"value": json.loads(key), "sample_count": count}
            for key, count in sorted(counts.items(), key=lambda item: item[1], reverse=True)[: args.top_values]
        ]
        special_values = []
        for value in values:
            if value is None:
                special_values.append(None)
            elif isinstance(value, str) and value.strip() in {"", "0", "-1", "9999-12-31", "9999-12-31 00:00:00"}:
                special_values.append(value)
            elif isinstance(value, (int, float)) and value in {0, -1}:
                special_values.append(value)
        columns.append(
            {
                "name": name,
                "type": col.get("type"),
                "nullable": col.get("nullable"),
                "sample_null_count": sum(1 for v in values if v is None),
                "sample_non_null_count": len(non_null),
                "sample_values": sample_values,
                "special_values_in_sample": list(dict.fromkeys(special_values)),
                "note": "基于有限样本，不代表全库分布",
            }
        )
    return {
        "schema": table.get("schema"),
        "table": table["name"],
        "sampled_rows": len(rows),
        "columns": columns,
        "rows": [{k: maybe_mask_sample(v, k, args.mask_sensitive) for k, v in row.items()} for row in rows[: args.include_rows]],
    }


def sqlite_profile(url: str, schema: Dict[str, Any], args: argparse.Namespace) -> Dict[str, Any]:
    sqlite_path = normalize_sqlite_path(url)
    if not sqlite_path:
        raise ValueError("不是 SQLite URL")
    con = sqlite3.connect(sqlite_path)
    con.row_factory = sqlite3.Row
    try:
        sampled = []
        for table in selected_tables(schema, args.tables, args.max_tables):
            name = table["name"]
            quoted = '"' + name.replace('"', '""') + '"'
            rows = [dict(row) for row in con.execute(f"select * from {quoted} limit ?", (args.sample_rows,)).fetchall()]
            sampled.append(summarize_sample(table, rows, args))
        return {
            "metadata": {
                "generated_at": utc_now(),
                "database_type": "sqlite",
                "scan_level": "table-sample",
                "sampling_policy": {
                    "max_tables": args.max_tables,
                    "max_columns": args.max_columns,
                    "sample_rows": args.sample_rows,
                    "mask_sensitive": args.mask_sensitive,
                    "counts_enabled": False,
                },
            },
            "tables": sampled,
        }
    finally:
        con.close()


def profile(args: argparse.Namespace) -> None:
    if args.schema:
        schema = read_json(args.schema)
    elif normalize_sqlite_path(args.url):
        schema = sqlite_introspect(args.url)
    else:
        try:
            schema = sqlalchemy_introspect(args.url)
        except Exception:
            if not is_postgres_like_url(args.url):
                raise
            schema = postgres_like_introspect(args.url)
    if normalize_sqlite_path(args.url):
        data = sqlite_profile(args.url, schema, args)
    else:
        try:
            data = sqlalchemy_profile(args.url, schema, args)
        except Exception:
            if not is_postgres_like_url(args.url):
                raise
            data = postgres_like_profile(args.url, schema, args)
    data["metadata"]["connection_source"] = maybe_mask_secret(args.url, args.mask_sensitive)
    write_json(data, args.output)


def sqlalchemy_profile(url: str, schema: Dict[str, Any], args: argparse.Namespace) -> Dict[str, Any]:
    try:
        from sqlalchemy import text
    except Exception as exc:  # pragma: no cover
        raise RuntimeError("缺少 SQLAlchemy。可安装到本地环境后重试：python3 -m pip install sqlalchemy") from exc
    engine = get_sqlalchemy_engine(url)
    preparer = engine.dialect.identifier_preparer

    def qname(table: Dict[str, Any]) -> str:
        name = preparer.quote(table["name"])
        schema_name = table.get("schema")
        if schema_name:
            return f"{preparer.quote_schema(schema_name)}.{name}"
        return name

    try:
        sampled = []
        with engine.connect() as con:
            for table in selected_tables(schema, args.tables, args.max_tables):
                full_name = qname(table)
                rows = [dict(row._mapping) for row in con.execute(text(f"select * from {full_name} limit {int(args.sample_rows)}")).fetchall()]
                sampled.append(summarize_sample(table, rows, args))
        return {
            "metadata": {
                "generated_at": utc_now(),
                "database_type": engine.dialect.name,
                "scan_level": "table-sample",
                "sampling_policy": {
                    "max_tables": args.max_tables,
                    "max_columns": args.max_columns,
                    "sample_rows": args.sample_rows,
                    "mask_sensitive": args.mask_sensitive,
                    "counts_enabled": False,
                },
            },
            "tables": sampled,
        }
    finally:
        engine.dispose()


def postgres_like_profile(url: str, schema: Dict[str, Any], args: argparse.Namespace) -> Dict[str, Any]:
    con = psycopg2_connect(url)
    try:
        cur = con.cursor()
        cur.execute("select version()")
        version = cur.fetchone()[0]
        sampled = []
        for table in selected_tables(schema, args.tables, args.max_tables):
            schema_name = table.get("schema")
            full_name = f"{pg_quote_ident(schema_name)}.{pg_quote_ident(table['name'])}" if schema_name else pg_quote_ident(table["name"])
            cur.execute(f"select * from {full_name} limit %s", (args.sample_rows,))
            col_names = [desc[0] for desc in cur.description]
            rows = [dict(zip(col_names, values)) for values in cur.fetchall()]
            sampled.append(summarize_sample(table, rows, args))
        return {
            "metadata": {
                "generated_at": utc_now(),
                "database_type": pg_database_type(version),
                "scan_level": "table-sample",
                "sampling_policy": {
                    "max_tables": args.max_tables,
                    "max_columns": args.max_columns,
                    "sample_rows": args.sample_rows,
                    "mask_sensitive": args.mask_sensitive,
                    "counts_enabled": False,
                },
            },
            "tables": sampled,
        }
    finally:
        con.close()


def analyze_field(args: argparse.Namespace) -> None:
    catalog = read_json(args.catalog)
    if "." not in args.field:
        raise ValueError("--field 必须使用 table.column 或 schema.table.column")
    parts = args.field.split(".")
    table_name = ".".join(parts[:-1])
    column_name = parts[-1]
    table = find_table(catalog, table_name)
    if column_name not in {col.get("name") for col in table.get("columns", [])}:
        raise ValueError(f"表 {table_name} 中不存在字段 {column_name}")

    temp_args = argparse.Namespace(
        tables=table_full_name(table),
        max_tables=1,
        max_columns=len(table.get("columns", [])),
        top_values=args.top_values,
        sample_rows=args.sample_rows,
        include_rows=args.include_rows,
        mask_sensitive=args.mask_sensitive,
    )
    if normalize_sqlite_path(args.url):
        sample_data = sqlite_profile(args.url, catalog, temp_args)
    else:
        try:
            sample_data = sqlalchemy_profile(args.url, catalog, temp_args)
        except Exception:
            if not is_postgres_like_url(args.url):
                raise
            sample_data = postgres_like_profile(args.url, catalog, temp_args)

    table_sample = sample_data.get("tables", [{}])[0]
    field_summary = next((col for col in table_sample.get("columns", []) if col.get("name") == column_name), None)
    sample_values = [row.get(column_name) for row in table_sample.get("rows", [])]
    write_json(
        {
            "metadata": {
                "generated_at": utc_now(),
                "scan_level": "field-sample",
                "database_type": sample_data.get("metadata", {}).get("database_type"),
                "connection_source": maybe_mask_secret(args.url, args.mask_sensitive),
                "sampling_policy": {
                    "sample_rows": args.sample_rows,
                    "mask_sensitive": args.mask_sensitive,
                    "counts_enabled": False,
                },
            },
            "table": table_full_name(table),
            "field": column_name,
            "schema": next((col for col in table.get("columns", []) if col.get("name") == column_name), {}),
            "sample_summary": field_summary,
            "sample_values": sample_values,
            "note": "字段分析基于有限样本，语义判断需 Agent 结合代码和业务上下文完成",
        },
        args.output,
    )


def singular(name: str) -> str:
    return name[:-1] if name.endswith("s") else name


def infer(args: argparse.Namespace) -> None:
    schema = read_json(args.schema)
    tables = schema.get("tables", [])
    table_names = {t["name"]: t for t in tables}
    pk_by_table = {t["name"]: set(t.get("primary_key") or []) for t in tables}
    candidates = []
    for table in tables:
        for col in table.get("columns", []):
            col_name = col.get("name", "")
            if not (col_name.endswith("_id") or col_name.endswith("_code")):
                continue
            base = re.sub(r"_(id|code)$", "", col_name)
            possible_tables = {base, base + "s", singular(base)}
            for target in sorted(possible_tables & set(table_names)):
                candidates.append(
                    {
                        "from_table": table["name"],
                        "from_column": col_name,
                        "to_table": target,
                        "to_columns": list(pk_by_table.get(target) or ["id"]),
                        "confidence": "low",
                        "evidence": ["字段命名匹配，尚未做数据覆盖率验证"],
                    }
                )
    write_json({"metadata": {"generated_at": utc_now()}, "relationship_findings": candidates}, args.output)


def export_evidence(args: argparse.Namespace) -> None:
    schema = read_json(args.catalog or args.schema) if (args.catalog or args.schema) else {}
    profile_data = read_json(args.samples or args.profile) if (args.samples or args.profile) else {}
    domain_plan = read_json(args.domain_plan) if args.domain_plan else {}
    relations = read_json(args.relations) if args.relations else {}
    tables = []
    sampled_names = {t.get("table") for t in profile_data.get("tables", [])}
    planned_names = {
        item.get("table")
        for item in domain_plan.get("tables", [])
        if item.get("suggested_next_step") == "sample-table"
    }
    for table in schema.get("tables", []):
        if likely_system_table(table):
            continue
        full_name = table_full_name(table)
        if planned_names and full_name not in planned_names and table.get("name") not in sampled_names:
            continue
        columns = table.get("columns", [])
        risk_cols = [
            c.get("name")
            for c in columns
            if re.search(r"status|type|amount|balance|point|score|stock|tenant|shop|store|expire|valid|delete|shard|version", c.get("name", ""), re.I)
        ]
        tables.append(
            {
                "table": table.get("name"),
                "schema": table.get("schema"),
                "role": "待业务域确认",
                "domain": None,
                "why_critical": ["包含高风险字段"] if risk_cols else [],
                "risk_columns": risk_cols,
                "field_analysis_status": {
                    "cataloged": True,
                    "sampled": table.get("name") in sampled_names,
                    "analyzed": [],
                    "not_analyzed": [c.get("name") for c in columns],
                },
                "doc_target": None,
            }
        )
    evidence = {
        "metadata": {
            "generated_at": utc_now(),
            "database_type": (schema.get("metadata") or {}).get("database_type", "unknown"),
            "connection_source": (schema.get("metadata") or {}).get("connection_source"),
            "sampling_policy": (profile_data.get("metadata") or {}).get("sampling_policy"),
            "scan_level": "evidence-pack",
        },
        "domains": [{"domain": domain_plan.get("domain"), "plan": domain_plan.get("tables", [])}] if domain_plan else [],
        "tables": tables,
        "field_findings": [],
        "relationship_findings": relations.get("relationship_findings", []),
        "guide_candidates": [],
        "doc_targets": [],
        "coverage": {
            "catalog_table_count": len(schema.get("tables", [])),
            "sampled_table_count": len(profile_data.get("tables", [])),
            "critical_tables_need_agent_analysis": [t["table"] for t in tables if t["why_critical"]],
            "notes": ["脚本只生成证据骨架；业务域划分和关键表逐字段语义需 Agent 结合代码、catalog 和有限样本补齐"],
        },
    }
    write_json(evidence, args.output)


def summarize_catalog(args: argparse.Namespace) -> None:
    catalog = read_json(args.catalog)
    domain_hints = read_json(args.domain_hints) if args.domain_hints else {}
    domain_plans = [read_json(path) for path in (args.domain_plan or [])]

    business_tables = [table for table in catalog.get("tables", []) if not likely_system_table(table)]
    schema_counts: Dict[str, int] = {}
    common_columns: Dict[str, int] = {}
    wide_tables = []
    risk_tables = []
    risk_re = re.compile(
        r"status|type|amount|balance|bonus|point|score|stock|tenant|group|project|pool|shop|store|expire|valid|delete|shard|version|level|grade|rule|action",
        re.I,
    )

    for table in business_tables:
        schema_name = table.get("schema") or "default"
        schema_counts[schema_name] = schema_counts.get(schema_name, 0) + 1
        columns = table.get("columns", [])
        for col in columns:
            name = col.get("name")
            if name:
                common_columns[name] = common_columns.get(name, 0) + 1
        if len(columns) >= args.wide_table_threshold:
            wide_tables.append({"table": table_full_name(table), "column_count": len(columns)})
        risk_columns = [col.get("name") for col in columns if risk_re.search(col.get("name", ""))]
        if risk_columns:
            risk_tables.append(
                {
                    "table": table_full_name(table),
                    "risk_column_count": len(risk_columns),
                    "risk_columns": risk_columns[: args.max_risk_columns],
                }
            )

    plan_summaries = []
    for plan in domain_plans:
        plan_summaries.append(
            {
                "domain": plan.get("domain"),
                "keywords": plan.get("keywords", []),
                "candidate_tables": [
                    {
                        "table": item.get("table"),
                        "match_score": item.get("match_score"),
                        "risk_columns": item.get("risk_columns", [])[: args.max_risk_columns],
                        "suggested_next_step": item.get("suggested_next_step"),
                    }
                    for item in plan.get("tables", [])[: args.max_tables_per_domain]
                ],
                "note": "只代表后续领域 KB 生成前的细扫候选；本命令未读取任何行级数据",
            }
        )

    hint_summaries = []
    for item in domain_hints.get("domain_hints", [])[: args.max_domain_hints]:
        hint_summaries.append(
            {
                "hint": item.get("hint"),
                "table_count": item.get("table_count"),
                "tables": item.get("tables", [])[: args.max_tables_per_domain],
            }
        )

    common_column_summaries = [
        {"column": name, "table_count": count}
        for name, count in sorted(common_columns.items(), key=lambda item: item[1], reverse=True)[: args.max_common_columns]
        if count >= args.min_common_column_tables
    ]

    write_json(
        {
            "metadata": {
                "generated_at": utc_now(),
                "scan_level": "catalog-summary",
                "source_catalog": args.catalog,
                "source_domain_hints": args.domain_hints,
                "source_domain_plans": args.domain_plan or [],
                "row_data_accessed": False,
                "counts_enabled": False,
            },
            "catalog_summary": {
                "database_type": (catalog.get("metadata") or {}).get("database_type"),
                "total_catalog_entries": len(catalog.get("tables", [])),
                "business_table_count": len(business_tables),
                "schema_counts": dict(sorted(schema_counts.items())),
            },
            "domain_hints": hint_summaries,
            "cross_domain_patterns": {
                "common_columns": common_column_summaries,
                "wide_tables_need_field_review": sorted(wide_tables, key=lambda item: item["column_count"], reverse=True)[: args.max_wide_tables],
                "risk_column_tables": sorted(risk_tables, key=lambda item: item["risk_column_count"], reverse=True)[: args.max_risk_tables],
            },
            "domain_scan_plans": plan_summaries,
            "explicitly_not_done": [
                "未读取行级数据",
                "未执行 sample-table/profile/analyze-field",
                "未执行 count/count distinct/全库画像",
                "未生成项目长期文档",
            ],
            "note": "这是 catalog-only 摘要，供 Agent 生成知识边界报告；真实字段语义仍需在具体领域 KB 生成前按需 sample/analyze",
        },
        args.output,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="只读数据库证据挖掘工具")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("discover-config", help="扫描项目中的数据库连接候选")
    p.add_argument("--root", default=".")
    p.add_argument("--max-file-bytes", type=int, default=512_000)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=discover_config)

    p = sub.add_parser("test-connection", help="测试只读连接")
    p.add_argument("--url", required=True)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=test_connection)

    p = sub.add_parser("catalog", help="读取轻量表/字段目录；默认不扫数据")
    p.add_argument("--url", required=True)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=introspect)

    p = sub.add_parser("introspect", help="兼容旧命令：等同 catalog")
    p.add_argument("--url", required=True)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=introspect)

    p = sub.add_parser("classify-catalog", help="基于 catalog 生成轻量业务域候选")
    p.add_argument("--catalog", required=True)
    p.add_argument("--output")
    p.set_defaults(func=classify_catalog)

    p = sub.add_parser("plan-domain-scan", help="按业务域关键词生成后续细扫计划")
    p.add_argument("--catalog", required=True)
    p.add_argument("--domain", required=True)
    p.add_argument("--keywords", help="逗号分隔的业务关键词")
    p.add_argument("--max-tables", type=int, default=30)
    p.add_argument("--output")
    p.set_defaults(func=plan_domain_scan)

    p = sub.add_parser("summarize-catalog", help="汇总 catalog/domain-plan 为目录级报告；不读取行级数据")
    p.add_argument("--catalog", required=True)
    p.add_argument("--domain-hints")
    p.add_argument("--domain-plan", action="append", help="可重复传入多个 plan-domain-scan 输出")
    p.add_argument("--wide-table-threshold", type=int, default=30)
    p.add_argument("--min-common-column-tables", type=int, default=5)
    p.add_argument("--max-domain-hints", type=int, default=20)
    p.add_argument("--max-tables-per-domain", type=int, default=20)
    p.add_argument("--max-common-columns", type=int, default=30)
    p.add_argument("--max-wide-tables", type=int, default=30)
    p.add_argument("--max-risk-tables", type=int, default=30)
    p.add_argument("--max-risk-columns", type=int, default=20)
    p.add_argument("--output")
    p.set_defaults(func=summarize_catalog)

    p = sub.add_parser("sample-table", help="对指定表抽少量样本；默认不做 count/distinct")
    p.add_argument("--url", required=True)
    p.add_argument("--catalog", "--schema", dest="schema")
    p.add_argument("--tables")
    p.add_argument("--max-tables", type=int, default=10)
    p.add_argument("--max-columns", type=int, default=80)
    p.add_argument("--top-values", type=int, default=10)
    p.add_argument("--sample-rows", type=int, default=30)
    p.add_argument("--include-rows", type=int, default=5)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=profile)

    p = sub.add_parser("profile", help="兼容旧命令：等同 sample-table，不做全表统计")
    p.add_argument("--url", required=True)
    p.add_argument("--catalog", "--schema", dest="schema")
    p.add_argument("--tables")
    p.add_argument("--max-tables", type=int, default=10)
    p.add_argument("--max-columns", type=int, default=80)
    p.add_argument("--top-values", type=int, default=10)
    p.add_argument("--sample-rows", type=int, default=30)
    p.add_argument("--include-rows", type=int, default=5)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=profile)

    p = sub.add_parser("analyze-field", help="对指定字段做有限样本点查")
    p.add_argument("--url", required=True)
    p.add_argument("--catalog", required=True)
    p.add_argument("--field", required=True, help="table.column 或 schema.table.column")
    p.add_argument("--top-values", type=int, default=10)
    p.add_argument("--sample-rows", type=int, default=50)
    p.add_argument("--include-rows", type=int, default=20)
    p.add_argument("--mask-sensitive", action="store_true", help="显式启用脱敏；默认保留测试环境原值")
    p.add_argument("--output")
    p.set_defaults(func=analyze_field)

    p = sub.add_parser("infer", help="从 schema 推断弱关系候选")
    p.add_argument("--catalog", "--schema", dest="schema", required=True)
    p.add_argument("--output")
    p.set_defaults(func=infer)

    p = sub.add_parser("export-evidence", help="合并 catalog/domain-plan/samples/relations 为证据包骨架")
    p.add_argument("--catalog")
    p.add_argument("--schema")
    p.add_argument("--domain-plan")
    p.add_argument("--samples")
    p.add_argument("--profile")
    p.add_argument("--relations")
    p.add_argument("--output")
    p.set_defaults(func=export_evidence)
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        args.func(args)
        return 0
    except Exception as exc:
        print(json.dumps({"ok": False, "error": str(exc)}, ensure_ascii=False), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
