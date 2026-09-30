#!/usr/bin/env python3
"""ServiceNow developer helper.

Generates safe starter queries and templates, lints ServiceNow scripts, and
validates this skill's bundled references.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


TABLE_MAP = {
    "incident": "incident",
    "incidents": "incident",
    "problem": "problem",
    "problems": "problem",
    "change": "change_request",
    "changes": "change_request",
    "change request": "change_request",
    "change requests": "change_request",
    "request": "sc_request",
    "requests": "sc_request",
    "request item": "sc_req_item",
    "request items": "sc_req_item",
    "req item": "sc_req_item",
    "req items": "sc_req_item",
    "task": "task",
    "tasks": "task",
    "user": "sys_user",
    "users": "sys_user",
    "group": "sys_user_group",
    "groups": "sys_user_group",
    "knowledge": "kb_knowledge",
    "knowledge article": "kb_knowledge",
    "knowledge articles": "kb_knowledge",
    "kb": "kb_knowledge",
    "asset": "alm_asset",
    "assets": "alm_asset",
    "software entitlement": "alm_license",
    "software entitlements": "alm_license",
    "software install": "cmdb_sam_sw_install",
    "software installs": "cmdb_sam_sw_install",
    "software model": "cmdb_software_product_model",
    "software models": "cmdb_software_product_model",
    "work order": "wm_order",
    "work orders": "wm_order",
    "case": "case",
    "cases": "case",
    "hr case": "sn_hr_core_case",
    "hr cases": "sn_hr_core_case",
    "customer case": "sn_customerservice_case",
    "customer cases": "sn_customerservice_case",
    "catalog item": "sc_cat_item",
    "catalog items": "sc_cat_item",
    "ci": "cmdb_ci",
    "cis": "cmdb_ci",
    "server": "cmdb_ci_server",
    "servers": "cmdb_ci_server",
    "vulnerability": "sn_vul_vulnerable_item",
    "vulnerabilities": "sn_vul_vulnerable_item",
    "vulnerable item": "sn_vul_vulnerable_item",
    "vulnerable items": "sn_vul_vulnerable_item",
    "vulnerability group": "sn_vul_group",
    "vulnerability groups": "sn_vul_group",
    "security incident": "sn_si_incident",
    "security incidents": "sn_si_incident",
    "risk": "sn_risk_risk",
    "risks": "sn_risk_risk",
    "control": "sn_compliance_control",
    "controls": "sn_compliance_control",
    "project": "pm_project",
    "projects": "pm_project",
    "portfolio": "pm_portfolio",
    "portfolios": "pm_portfolio",
    "demand": "dmn_demand",
    "demands": "dmn_demand",
    "business application": "cmdb_ci_business_app",
    "business applications": "cmdb_ci_business_app",
    "business service": "cmdb_ci_service",
    "business services": "cmdb_ci_service",
    "application service": "cmdb_ci_service_auto",
    "application services": "cmdb_ci_service_auto",
    "service offering": "service_offering",
    "service offerings": "service_offering",
}

PRIORITY_MAP = {
    "critical": "1",
    "high": "2",
    "medium": "3",
    "moderate": "3",
    "low": "4",
    "planning": "5",
}

SKILL_FRONTMATTER_REQUIRED = ("name", "description")
DEFAULT_LIMIT = 100


@dataclass
class QueryFilter:
    kind: str
    field: str | None = None
    operator: str | None = None
    value: str | None = None
    raw: bool = False


@dataclass
class Issue:
    line: int
    severity: str
    message: str
    code: str


BASE_LINT_RULES = [
    {
        "pattern": r"getXMLWait\s*\(",
        "message": "CRITICAL: getXMLWait() blocks the UI thread. Use getXMLAnswer() with a callback instead.",
        "severity": "error",
    },
    {
        "pattern": r"\beval\s*\(",
        "message": "CRITICAL: eval() is a security risk and banned in ServiceNow. Use Script Includes instead.",
        "severity": "error",
    },
    {
        "pattern": r"['\"][a-f0-9]{32}['\"]",
        "message": "WARNING: Possible hardcoded sys_id found. Prefer properties, named records, or dynamic lookups.",
        "severity": "warning",
    },
    {
        "pattern": r"\.getRowCount\s*\(",
        "message": "PERFORMANCE: getRowCount() loads matching records. Use GlideAggregate with addAggregate('COUNT') instead.",
        "severity": "warning",
    },
    {
        "pattern": r"gs\.log\s*\(",
        "message": "DEPRECATED: gs.log() is deprecated. Use gs.info(), gs.warn(), gs.error(), or gs.debug() instead.",
        "severity": "warning",
    },
    {
        "pattern": r"gs\.sleep\s*\(",
        "message": "PERFORMANCE: gs.sleep() blocks the worker thread. Prefer async rules, events, or scheduled jobs.",
        "severity": "warning",
    },
    {
        "pattern": r"\b(g_form|g_user|g_list)\.",
        "message": "INFO: Client-side API detected. Ensure this code runs in a client context, not a server script.",
        "severity": "info",
    },
    {
        "pattern": r"addEncodedQuery\s*\(\s*\w+\s*\)",
        "message": "SECURITY: addEncodedQuery() is receiving a variable. Sanitize user input before using it in encoded queries.",
        "severity": "warning",
    },
    {
        "pattern": r"\.deleteMultiple\s*\(",
        "message": "CAUTION: deleteMultiple() bypasses Business Rules. Make sure that is intentional.",
        "severity": "info",
    },
    {
        "pattern": r"\.updateMultiple\s*\(",
        "message": "CAUTION: updateMultiple() bypasses Business Rules. Make sure that is intentional.",
        "severity": "info",
    },
    {
        "pattern": r"new\s+Packages\.",
        "message": "WARNING: Java Packages are deprecated and blocked in scoped apps. Prefer supported platform APIs.",
        "severity": "warning",
    },
    {
        "pattern": r"setBasicAuth\s*\(\s*['\"]username['\"]\s*,\s*['\"]password['\"]\s*\)",
        "message": "SECURITY: Placeholder basic-auth credentials found. Configure auth on the REST Message or use a credential alias/property-backed value.",
        "severity": "error",
    },
    {
        "pattern": r"setAuthenticationProfile\s*\(\s*['\"]oauth2['\"]\s*,\s*['\"][^'\"]+sys_id['\"]\s*\)",
        "message": "SECURITY: OAuth profile placeholder looks hardcoded. Prefer a property-backed profile name or configure auth on the REST Message method.",
        "severity": "error",
    },
]


def js_quote(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace("'", "\\'")
        .replace("\r", "\\r")
        .replace("\n", "\\n")
    )
    return f"'{escaped}'"


def normalize_space(value: str) -> str:
    return re.sub(r"\s+", " ", value.strip())


def strip_wrapping_quotes(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
        return value[1:-1].strip()
    return value


def _resolve_table(name: str) -> str:
    normalized = normalize_space(name).lower()
    if normalized in TABLE_MAP:
        return TABLE_MAP[normalized]

    singular = normalized[:-1] if normalized.endswith("s") else normalized
    if singular in TABLE_MAP:
        return TABLE_MAP[singular]

    return normalized.replace(" ", "_")


def _priority_value(value: str) -> str:
    normalized = value.strip().lower()
    return PRIORITY_MAP.get(normalized, normalized)


def _extract_table(description: str) -> str:
    lower = description.lower()
    for key in sorted(TABLE_MAP, key=len, reverse=True):
        if re.search(rf"\b{re.escape(key)}\b", lower):
            return TABLE_MAP[key]
    return "incident"


def _render_filter(target: str, query_filter: QueryFilter) -> str:
    if query_filter.kind == "active":
        return f"{target}.addActiveQuery();"
    if query_filter.kind == "null":
        return f"{target}.addNullQuery({js_quote(query_filter.field or '')});"
    if query_filter.kind == "encoded":
        return f"{target}.addEncodedQuery({js_quote(query_filter.value or '')});"
    if query_filter.kind == "query":
        assert query_filter.field is not None
        if query_filter.operator:
            rendered_value = query_filter.value or ""
            if query_filter.raw:
                return f"{target}.addQuery({js_quote(query_filter.field)}, {js_quote(query_filter.operator)}, {rendered_value});"
            return f"{target}.addQuery({js_quote(query_filter.field)}, {js_quote(query_filter.operator)}, {js_quote(rendered_value)});"
        if query_filter.raw:
            return f"{target}.addQuery({js_quote(query_filter.field)}, {query_filter.value or ''});"
        return f"{target}.addQuery({js_quote(query_filter.field)}, {js_quote(query_filter.value or '')});"
    raise ValueError(f"Unknown filter kind: {query_filter.kind}")


def _build_record_query(
    table: str,
    filters: Iterable[QueryFilter],
    *,
    order: str | None = None,
    desc: bool = False,
    limit: int = DEFAULT_LIMIT,
) -> str:
    lines = [f"var gr = new GlideRecord({js_quote(_resolve_table(table))});"]
    lines.extend(_render_filter("gr", query_filter) for query_filter in filters)
    if order:
        lines.append(f"gr.{'orderByDesc' if desc else 'orderBy'}({js_quote(order)});")
    lines.append(f"gr.setLimit({limit});")
    lines.append("gr.query();")
    lines.append("while (gr.next()) {")
    lines.append("    var primary = gr.getValue('number') || gr.getValue('name') || gr.getValue('display_name') || gr.getDisplayValue();")
    lines.append("    var secondary = gr.getValue('short_description') || gr.getValue('source') || gr.getValue('asset_tag') || '';")
    lines.append("    if (!gs.nil(secondary)) {")
    lines.append("        gs.info(primary + ': ' + secondary);")
    lines.append("    } else {")
    lines.append("        gs.info(primary);")
    lines.append("    }")
    lines.append("}")
    return "\n".join(lines)


def _build_count_query(table: str, filters: Iterable[QueryFilter]) -> str:
    lines = [f"var ga = new GlideAggregate({js_quote(_resolve_table(table))});"]
    lines.extend(_render_filter("ga", query_filter) for query_filter in filters)
    lines.append("ga.addAggregate('COUNT');")
    lines.append("ga.query();")
    lines.append("if (ga.next()) {")
    lines.append("    gs.info('Count: ' + ga.getAggregate('COUNT'));")
    lines.append("}")
    return "\n".join(lines)


def _query_active_assigned_to_me(match: re.Match[str]) -> str:
    return _build_record_query(
        match.group("table"),
        [
            QueryFilter("active"),
            QueryFilter("query", "assigned_to", value="gs.getUserID()", raw=True),
        ],
        order="sys_created_on",
        desc=True,
    )


def _query_by_priority(match: re.Match[str]) -> str:
    return _build_record_query(
        match.group("table"),
        [QueryFilter("query", "priority", value=_priority_value(match.group("priority")))],
    )


def _query_active(match: re.Match[str]) -> str:
    return _build_record_query(match.group("table"), [QueryFilter("active")])


def _query_last_n_days(match: re.Match[str]) -> str:
    return _build_record_query(
        match.group("table"),
        [QueryFilter("query", "sys_created_on", ">=", f"gs.daysAgoStart({match.group('days')})", raw=True)],
    )


def _query_unassigned(match: re.Match[str]) -> str:
    return _build_record_query(match.group("table"), [QueryFilter("null", "assigned_to")])


def _count_active(match: re.Match[str]) -> str:
    return _build_count_query(match.group("table"), [QueryFilter("active")])


def _query_group(match: re.Match[str]) -> str:
    group_name = strip_wrapping_quotes(match.group("group"))
    return _build_record_query(
        match.group("table"),
        [QueryFilter("query", "assignment_group.name", value=group_name)],
    )


def _query_state(match: re.Match[str]) -> str:
    state_name = strip_wrapping_quotes(match.group("state"))
    return _build_record_query(
        match.group("table"),
        [QueryFilter("query", "state", value=state_name)],
    )


def _query_this_week(match: re.Match[str]) -> str:
    return _build_record_query(
        match.group("table"),
        [
            QueryFilter(
                "encoded",
                value="sys_created_onONThis week@javascript:gs.beginningOfThisWeek()@javascript:gs.endOfThisWeek()",
            )
        ],
        order="sys_created_on",
        desc=True,
    )


QUERY_PATTERNS = [
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?active\s+(?P<table>.+?)\s+assigned\s+to\s+(?:me|current\s+user)\s*$",
            re.IGNORECASE,
        ),
        _query_active_assigned_to_me,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?P<table>.+?)\s+(?:where|with)\s+priority\s+(?:is\s+)?(?P<priority>\d|critical|high|medium|moderate|low|planning)\s*$",
            re.IGNORECASE,
        ),
        _query_by_priority,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?active\s+(?P<table>.+?)\s*$",
            re.IGNORECASE,
        ),
        _query_active,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?P<table>.+?)\s+(?:created|opened)\s+(?:in\s+the\s+)?last\s+(?P<days>\d+)\s+days?\s*$",
            re.IGNORECASE,
        ),
        _query_last_n_days,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?unassigned\s+(?P<table>.+?)\s*$",
            re.IGNORECASE,
        ),
        _query_unassigned,
    ),
    (
        re.compile(
            r"(?:count|how\s+many)\s+active\s+(?P<table>.+?)\s*$",
            re.IGNORECASE,
        ),
        _count_active,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?P<table>.+?)\s+assigned\s+to\s+group\s+(?P<group>.+?)\s*$",
            re.IGNORECASE,
        ),
        _query_group,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?P<table>.+?)\s+in\s+state\s+(?P<state>.+?)\s*$",
            re.IGNORECASE,
        ),
        _query_state,
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?:p1|priority\s+1)\s+(?P<table>.+?)\s+(?:opened|created)\s+this\s+week\s*$",
            re.IGNORECASE,
        ),
        lambda match: _build_record_query(
            match.group("table"),
            [
                QueryFilter("query", "priority", value="1"),
                QueryFilter(
                    "encoded",
                    value="sys_created_onONThis week@javascript:gs.beginningOfThisWeek()@javascript:gs.endOfThisWeek()",
                ),
            ],
            order="sys_created_on",
            desc=True,
        ),
    ),
    (
        re.compile(
            r"(?:find|get|show|list)\s+(?:all\s+)?(?P<table>.+?)\s+(?:opened|created)\s+this\s+week\s*$",
            re.IGNORECASE,
        ),
        _query_this_week,
    ),
]


def generate_query(description: str) -> str:
    normalized = normalize_space(description)
    for pattern, handler in QUERY_PATTERNS:
        match = pattern.search(normalized)
        if match:
            return handler(match)
    return _build_record_query(_extract_table(normalized), [QueryFilter("active")])


def template_business_rule(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    when = args.when or "before"
    ops = []
    if args.insert:
        ops.append("Insert")
    if args.update:
        ops.append("Update")
    if args.delete:
        ops.append("Delete")
    if args.query:
        ops.append("Query")
    if not ops:
        ops = ["Insert", "Update"]

    when_comment = {
        "before": "Mutate current with setValue() and avoid current.update().",
        "after": "Prefer events, child-record creation, or async follow-up work.",
        "async": "Heavy processing only; previous is not reliable here.",
        "display": "Populate g_scratchpad for client consumers.",
    }[when]

    example_logic = {
        "before": """    if (current.state.changesTo('6') && gs.nil(current.getValue('close_notes'))) {
        gs.addErrorMessage('Close notes are required before resolving this record.');
        current.setAbortAction(true);
        return;
    }""",
        "after": """    if (current.state.changesTo('2')) {
        gs.eventQueue('x_scope.record.in_progress', current, current.getUniqueValue(), current.getValue('number'));
    }""",
        "async": """    try {
        var eventPayload = JSON.stringify({
            number: current.getValue('number'),
            table: current.getTableName()
        });
        gs.eventQueue('x_scope.record.sync_requested', current, eventPayload, '');
    } catch (e) {
        gs.error('Async follow-up failed: ' + e.message);
    }""",
        "display": """    g_scratchpad.recordNumber = current.getValue('number');
    g_scratchpad.canEdit = current.canWrite();""",
    }[when]

    return f"""// Business Rule: [Name]
// Table: {table}
// When: {when}
// Operations: {', '.join(ops)}
// Condition: [set via condition builder]
// Order: 100

(function executeRule(current, previous /* null when async */) {{
    // {when.upper()} rule
    // {when_comment}

{example_logic}
}})(current, previous);"""


def template_script_include(args: argparse.Namespace) -> str:
    name = args.name or "MyScriptInclude"
    if args.client_callable:
        return f"""var {name} = Class.create();
{name}.prototype = Object.extendsObject(AbstractAjaxProcessor, {{
    myMethod: function() {{
        var recordSysId = this.getParameter('sysparm_record_sys_id');
        if (gs.nil(recordSysId)) {{
            return JSON.stringify({{ success: false, error: 'Missing sysparm_record_sys_id' }});
        }}

        var gr = new GlideRecord('incident');
        if (!gr.get(recordSysId)) {{
            return JSON.stringify({{ success: false, error: 'Record not found' }});
        }}

        return JSON.stringify({{
            success: true,
            display_value: gr.getDisplayValue(),
            number: gr.getValue('number'),
            name: gr.getValue('name'),
            short_description: gr.getValue('short_description')
        }});
    }},

    type: '{name}'
}});"""

    return f"""var {name} = Class.create();
{name}.prototype = {{
    initialize: function() {{
    }},

    getOpenRecordsForUser: function(userSysId) {{
        var records = [];
        var gr = new GlideRecord('incident');
        gr.addActiveQuery();
        gr.addQuery('assigned_to', userSysId);
        gr.setLimit(25);
        gr.query();

        while (gr.next()) {{
            records.push({{
                sys_id: gr.getUniqueValue(),
                number: gr.getValue('number'),
                short_description: gr.getValue('short_description')
            }});
        }}

        return records;
    }},

    type: '{name}'
}};"""


def template_client_script(args: argparse.Namespace) -> str:
    cs_type = args.type or "onChange"
    table = args.table or "incident"
    field = args.field or "state"

    templates = {
        "onChange": f"""// Client Script: [Name]
// Type: onChange | Table: {table} | Field: {field}

function onChange(control, oldValue, newValue, isLoading, isTemplate) {{
    if (isLoading || newValue === '') {{
        return;
    }}

    if (newValue === '6') {{
        g_form.setMandatory('close_code', true);
        g_form.setMandatory('close_notes', true);
    }} else {{
        g_form.setMandatory('close_code', false);
        g_form.setMandatory('close_notes', false);
    }}
}}""",
        "onLoad": f"""// Client Script: [Name]
// Type: onLoad | Table: {table}

function onLoad() {{
    if (g_scratchpad && g_scratchpad.bannerMessage) {{
        g_form.addInfoMessage(g_scratchpad.bannerMessage);
    }}

    if (g_form.isNewRecord()) {{
        g_form.setValue('contact_type', 'self-service');
    }}
}}""",
        "onSubmit": f"""// Client Script: [Name]
// Type: onSubmit | Table: {table}

function onSubmit() {{
    var shortDesc = g_form.getValue('short_description');
    if (shortDesc.length < 10) {{
        g_form.addErrorMessage('Short description must be at least 10 characters.');
        return false;
    }}
    return true;
}}""",
        "onCellEdit": f"""// Client Script: [Name]
// Type: onCellEdit | Table: {table}

function onCellEdit(sysIDs, table, oldValues, newValue, callback) {{
    if (sysIDs.length > 10) {{
        callback({{
            status: 'error',
            error_message: 'Cannot bulk edit more than 10 records at once.'
        }});
        return false;
    }}

    callback({{ status: 'success' }});
    return true;
}}""",
    }
    return templates[cs_type]


def template_rest_message(args: argparse.Namespace) -> str:
    method = (args.method or "GET").upper()
    auth = args.auth or "basic"

    auth_comment = (
        "// Preferred: configure OAuth2 on the REST Message method record and keep credentials out of script."
        if auth == "oauth2"
        else "// Preferred: configure credentials on the REST Message or use a credential alias/property-backed value."
    )
    auth_setup = (
        "var oauthProfile = gs.getProperty('x_scope.outbound.oauth_profile', 'x_scope.default_oauth_profile');\n"
        "    rm.setAuthenticationProfile('oauth2', oauthProfile);"
        if auth == "oauth2"
        else "// rm.setStringParameterNoEscape('credential_alias', gs.getProperty('x_scope.credential_alias'));"
    )

    request_body = (
        """rm.setRequestBody(JSON.stringify({
        number: current.getValue('number'),
        short_description: current.getValue('short_description')
    }));"""
        if method in {"POST", "PUT", "PATCH"}
        else "// rm.setQueryParameter('sys_id', current.getUniqueValue());"
    )

    return f"""// Outbound REST Message — {method} with {auth} authentication
// Recommended setup:
// 1. Create a REST Message record and method.
// 2. Configure authentication on the method record or through properties.
// 3. Keep credentials and profile names out of source control.

try {{
    var restMessageName = gs.getProperty('x_scope.outbound.rest_message_name', 'My REST Message');
    var restMethodName = gs.getProperty('x_scope.outbound.rest_method_name', '{method}');
    var rm = new sn_ws.RESTMessageV2(restMessageName, restMethodName);

    rm.setRequestHeader('Accept', 'application/json');
    rm.setRequestHeader('Content-Type', 'application/json');
    rm.setHttpTimeout(30000);

    {auth_comment}
    {auth_setup}

    {request_body}

    var response = rm.execute();
    var statusCode = response.getStatusCode();
    var responseBody = response.getBody();

    if (statusCode >= 200 && statusCode < 300) {{
        gs.info('REST call successful: ' + statusCode);
    }} else {{
        gs.error('REST call failed: ' + statusCode + ' ' + responseBody);
    }}
}} catch (e) {{
    gs.error('REST exception: ' + e.message);
}}"""


def template_acl(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    acl_type = args.type or "record"
    operation = args.operation or "read"

    example = (
        f"answer = gs.hasRole('itil') && gs.getUser().isMemberOf(current.getValue('assignment_group'));"
        if acl_type == "record"
        else "answer = current.getValue('state') != '7'; // deny when closed"
    )

    return f"""// ACL Rule Configuration
// Type: {acl_type}
// Operation: {operation}
// Table: {table}
{"// Field: [specify field name]" if acl_type == "field" else "// Row-level ACL"}

(function() {{
    if (gs.hasRole('admin')) {{
        answer = true;
        return;
    }}

    {example}
}})();"""


def template_scripted_rest_api(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    return f"""// Scripted REST Resource: GET /api/x_scope/v1/{table}/{{sys_id}}
(function process(/*RESTAPIRequest*/ request, /*RESTAPIResponse*/ response) {{
    var sysId = request.pathParams.sys_id;
    if (gs.nil(sysId)) {{
        response.setStatus(400);
        response.setBody({{ error: 'Missing sys_id path parameter' }});
        return;
    }}

    var gr = new GlideRecord('{table}');
    if (!gr.get(sysId)) {{
        response.setStatus(404);
        response.setBody({{ error: 'Record not found' }});
        return;
    }}

    response.setStatus(200);
    response.setBody({{
        sys_id: gr.getUniqueValue(),
        display_value: gr.getDisplayValue(),
        number: gr.getValue('number'),
        name: gr.getValue('name'),
        short_description: gr.getValue('short_description')
    }});
}})(request, response);"""


def template_flow_script_action(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    return f"""(function execute(inputs, outputs) {{
    var ga = new GlideAggregate('{table}');
    ga.addActiveQuery();
    ga.addQuery('assignment_group', inputs.assignment_group);
    ga.addAggregate('COUNT');
    ga.query();

    outputs.active_count = ga.next() ? parseInt(ga.getAggregate('COUNT'), 10) : 0;
    outputs.should_notify = outputs.active_count > 10;
}})(inputs, outputs);"""


def template_integrationhub_action(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    return f"""// IntegrationHub custom action script step
// Inputs:
//   endpoint_path (String)
//   page_cursor (String, optional)
// Outputs:
//   status_code (Integer)
//   response_body (String)
//   next_cursor (String)
//   has_more (Boolean)

(function execute(inputs, outputs) {{
    try {{
        var baseUrl = gs.getProperty('x_scope.integration.base_url');
        if (gs.nil(baseUrl)) {{
            throw new Error('Missing x_scope.integration.base_url property');
        }}

        var rm = new sn_ws.RESTMessageV2();
        rm.setEndpoint(baseUrl + inputs.endpoint_path);
        rm.setHttpMethod('GET');
        rm.setRequestHeader('Accept', 'application/json');
        rm.setHttpTimeout(30000);

        // Prefer a Connection & Credential Alias or a configured REST Message method.
        // Keep auth material in platform configuration, not in script.
        if (!gs.nil(inputs.page_cursor)) {{
            rm.setQueryParameter('cursor', inputs.page_cursor);
        }}

        var response = rm.execute();
        outputs.status_code = response.getStatusCode();
        outputs.response_body = response.getBody();

        if (outputs.status_code < 200 || outputs.status_code >= 300) {{
            throw new Error('Upstream call failed: ' + outputs.status_code + ' ' + outputs.response_body);
        }}

        var payload = JSON.parse(outputs.response_body);
        outputs.next_cursor = payload.next_cursor || '';
        outputs.has_more = !gs.nil(outputs.next_cursor);
    }} catch (e) {{
        outputs.status_code = outputs.status_code || 500;
        outputs.response_body = JSON.stringify({{
            table: '{table}',
            error: e.message
        }});
        outputs.next_cursor = '';
        outputs.has_more = false;
        throw e;
    }}
}})(inputs, outputs);"""


def template_atf_server_test(args: argparse.Namespace) -> str:
    table = args.table or "incident"
    return f"""// ATF Server-side script step
(function(outputs, steps, params, stepResult, assertEqual) {{
    var gr = new GlideRecord('{table}');
    gr.addQuery('short_description', 'CONTAINS', params.expected_text);
    gr.setLimit(1);
    gr.query();

    assertEqual({{
        name: 'Expected record should exist',
        shouldbe: true,
        value: gr.next()
    }});

    stepResult.setOutputMessage('Validated presence of {table} test record.');
}})(outputs, steps, params, stepResult, assertEqual);"""


def _line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _line_text(lines: list[str], line_number: int) -> str:
    if 1 <= line_number <= len(lines):
        return lines[line_number - 1].strip()
    return ""


def _glide_record_variables(script: str) -> set[str]:
    return set(re.findall(r"(?:var|let|const)\s+(\w+)\s*=\s*new GlideRecord\s*\(", script))


def _find_base_pattern_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    for rule in BASE_LINT_RULES:
        for match in re.finditer(rule["pattern"], script, re.MULTILINE):
            line_number = _line_for_offset(script, match.start())
            issues.append(
                Issue(
                    line=line_number,
                    severity=rule["severity"],
                    message=rule["message"],
                    code=_line_text(lines, line_number),
                )
            )
    return issues


def _find_direct_assignment_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    targets = _glide_record_variables(script) | {"current"}
    if not targets:
        return issues

    target_pattern = "|".join(sorted(re.escape(target) for target in targets))
    pattern = re.compile(rf"\b({target_pattern})\.(\w+)\s*(?<![=!<>])=(?!=)")
    for match in pattern.finditer(script):
        line_number = _line_for_offset(script, match.start())
        if _line_text(lines, line_number).startswith("//"):
            continue
        issues.append(
            Issue(
                line=line_number,
                severity="warning",
                message="WARNING: Direct field assignment detected. Use setValue('field', value) for GlideRecord/current updates.",
                code=_line_text(lines, line_number),
            )
        )
    return issues


def _find_gliderecord_aggregate_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    glide_record_vars = _glide_record_variables(script)
    if not glide_record_vars:
        return issues

    pattern = re.compile(r"\b(\w+)\.addAggregate\s*\(")
    for match in pattern.finditer(script):
        if match.group(1) not in glide_record_vars:
            continue
        line_number = _line_for_offset(script, match.start())
        issues.append(
            Issue(
                line=line_number,
                severity="error",
                message="CRITICAL: addAggregate() is being called on GlideRecord. Use GlideAggregate instead.",
                code=_line_text(lines, line_number),
            )
        )
    return issues


def _find_query_without_filters_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    pattern = re.compile(
        r"(?:var|let|const)\s+(?P<var>\w+)\s*=\s*new GlideRecord\s*\([^)]+\);\s*(?P<body>[\s\S]{0,500}?)\b(?P=var)\.query\s*\(\s*\)",
        re.MULTILINE,
    )
    filter_markers = (
        ".addQuery(",
        ".addEncodedQuery(",
        ".addActiveQuery(",
        ".addNullQuery(",
        ".addNotNullQuery(",
        ".addJoinQuery(",
        ".get(",
    )
    for match in pattern.finditer(script):
        body = match.group("body")
        if any(marker in body for marker in filter_markers):
            continue
        line_number = _line_for_offset(script, match.start("var"))
        issues.append(
            Issue(
                line=line_number,
                severity="warning",
                message="WARNING: GlideRecord query appears to run without any filter conditions.",
                code=_line_text(lines, line_number),
            )
        )
    return issues


def _find_unchecked_get_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    glide_record_vars = _glide_record_variables(script)
    if not glide_record_vars:
        return issues

    bare_call = re.compile(r"^\s*(\w+)\.get\s*\([^)]+\)\s*;\s*$")
    for line_number, line in enumerate(lines, 1):
        match = bare_call.match(line)
        if not match or match.group(1) not in glide_record_vars:
            continue

        next_meaningful = ""
        for candidate in lines[line_number:]:
            stripped = candidate.strip()
            if stripped:
                next_meaningful = stripped
                break
        if next_meaningful.startswith("if"):
            continue

        issues.append(
            Issue(
                line=line_number,
                severity="warning",
                message="WARNING: GlideRecord.get() result is not checked. In scoped apps it returns a boolean.",
                code=line.strip(),
            )
        )
    return issues


def _find_nested_query_issues(script: str, lines: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    pattern = re.compile(r"while\s*\(\s*\w+\.next\(\)\s*\)\s*\{[\s\S]{0,400}?new GlideRecord\s*\(", re.MULTILINE)
    for match in pattern.finditer(script):
        line_number = _line_for_offset(script, match.start())
        issues.append(
            Issue(
                line=line_number,
                severity="warning",
                message="PERFORMANCE: GlideRecord created inside while(next()) loop. Consider batch querying to avoid N+1 patterns.",
                code=_line_text(lines, line_number),
            )
        )
    return issues


def lint_script(script: str) -> list[Issue]:
    lines = script.splitlines()
    issues = []
    issues.extend(_find_base_pattern_issues(script, lines))
    issues.extend(_find_direct_assignment_issues(script, lines))
    issues.extend(_find_gliderecord_aggregate_issues(script, lines))
    issues.extend(_find_query_without_filters_issues(script, lines))
    issues.extend(_find_unchecked_get_issues(script, lines))
    issues.extend(_find_nested_query_issues(script, lines))

    deduped: dict[tuple[int, str, str], Issue] = {}
    for issue in issues:
        deduped[(issue.line, issue.severity, issue.message)] = issue
    return sorted(
        deduped.values(),
        key=lambda issue: ({"error": 0, "warning": 1, "info": 2}[issue.severity], issue.line, issue.message),
    )


def format_lint_results(issues: list[Issue]) -> str:
    if not issues:
        return "✅ No issues found. Script looks clean!"

    counts = {"error": 0, "warning": 0, "info": 0}
    output = []
    for issue in issues:
        counts[issue.severity] += 1
        icon = {"error": "❌", "warning": "⚠️", "info": "ℹ️"}[issue.severity]
        output.append(f"  {icon} Line {issue.line}: {issue.message}")
        output.append(f"    → {issue.code}")
        output.append("")

    output.append("=" * 60)
    output.append(
        f"Found {len(issues)} issue(s): {counts['error']} error(s), {counts['warning']} warning(s), {counts['info']} info"
    )
    output.append("=" * 60)
    return "\n".join(output)


def _parse_frontmatter(skill_path: Path) -> tuple[dict[str, str], str]:
    text = skill_path.read_text()
    if not text.startswith("---\n"):
        raise ValueError("SKILL.md is missing YAML frontmatter opening delimiter.")

    parts = text.split("---\n", 2)
    if len(parts) < 3:
        raise ValueError("SKILL.md is missing YAML frontmatter closing delimiter.")

    raw_frontmatter = parts[1]
    body = parts[2]
    frontmatter: dict[str, str] = {}
    for line in raw_frontmatter.splitlines():
        if not line.strip() or line.startswith("metadata:") or line.startswith("  "):
            continue
        if ":" not in line:
            continue
        key, value = line.split(":", 1)
        frontmatter[key.strip()] = value.strip().strip('"')
    return frontmatter, body


def _extract_markdown_code_blocks(markdown: str) -> list[tuple[int, str]]:
    blocks = []
    pattern = re.compile(r"```(?:javascript|js)\n(.*?)```", re.DOTALL)
    for match in pattern.finditer(markdown):
        start_line = markdown.count("\n", 0, match.start()) + 1
        blocks.append((start_line, match.group(1)))
    return blocks


def validate_skill(skill_dir: str) -> list[str]:
    skill_path = Path(skill_dir)
    errors: list[str] = []

    skill_file = skill_path / "SKILL.md"
    if not skill_file.exists():
        return ["Missing SKILL.md"]

    try:
        frontmatter, body = _parse_frontmatter(skill_file)
    except ValueError as exc:
        return [str(exc)]

    for field in SKILL_FRONTMATTER_REQUIRED:
        if field not in frontmatter or not frontmatter[field]:
            errors.append(f"Frontmatter missing required field: {field}")

    name = frontmatter.get("name", "")
    if name and not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", name):
        errors.append("Frontmatter name must be kebab-case.")
    description = frontmatter.get("description", "")
    if description and len(description) > 1024:
        errors.append("Frontmatter description exceeds 1024 characters.")
    if description and "use when" not in description.lower():
        errors.append("Frontmatter description should include explicit 'Use when' trigger guidance.")
    if "<" in description or ">" in description:
        errors.append("Frontmatter description must not contain angle brackets.")

    if (skill_path / "README.md").exists():
        errors.append("Skill folder should not contain README.md; use SKILL.md or references/.")

    references_dir = skill_path / "references"
    if references_dir.exists():
        auth_placeholder_patterns = [
            re.compile(r"setBasicAuth\s*\(\s*['\"]username['\"]\s*,\s*['\"]password['\"]\s*\)"),
            re.compile(r"setAuthenticationProfile\s*\(\s*['\"]oauth2['\"]\s*,\s*['\"][^'\"]+sys_id['\"]\s*\)"),
        ]
        aggregate_pattern = re.compile(
            r"(?:var|let|const)\s+(\w+)\s*=\s*new GlideRecord\s*\([^)]+\);[\s\S]{0,400}?\b\1\.addAggregate\s*\(",
            re.MULTILINE,
        )
        bare_get_pattern = re.compile(r"^\s*(\w+)\.get\s*\([^)]+\)\s*;\s*$")

        for markdown_path in sorted(references_dir.glob("*.md")):
            markdown = markdown_path.read_text()

            for pattern in auth_placeholder_patterns:
                for match in pattern.finditer(markdown):
                    line_number = _line_for_offset(markdown, match.start())
                    errors.append(f"{markdown_path.name}:{line_number}: Unsafe auth placeholder should be removed.")

            for match in aggregate_pattern.finditer(markdown):
                line_number = _line_for_offset(markdown, match.start())
                errors.append(f"{markdown_path.name}:{line_number}: GlideRecord.addAggregate() detected; use GlideAggregate.")

            for start_line, block in _extract_markdown_code_blocks(markdown):
                block_lines = block.splitlines()
                glide_vars = _glide_record_variables(block)
                target_vars = glide_vars | {"current"}
                if target_vars:
                    target_pattern = "|".join(sorted(re.escape(target) for target in target_vars))
                    direct_assignment = re.compile(rf"\b({target_pattern})\.(\w+)\s*(?<![=!<>])=(?!=)")
                    for index, line in enumerate(block_lines, 1):
                        stripped = line.strip()
                        if stripped.startswith("//"):
                            continue
                        if direct_assignment.search(line):
                            errors.append(
                                f"{markdown_path.name}:{start_line + index - 1}: Direct assignment found in reference example."
                            )

                for index, line in enumerate(block_lines, 1):
                    match = bare_get_pattern.match(line)
                    if not match or match.group(1) not in glide_vars:
                        continue
                    errors.append(
                        f"{markdown_path.name}:{start_line + index - 1}: Bare GlideRecord.get() call should be checked before field access."
                    )

    if len(body.split()) > 5000:
        errors.append("SKILL.md body exceeds 5000 words; move detail into references/.")

    return errors


def _read_script_argument(file_path: str | None) -> str:
    if file_path:
        return Path(file_path).read_text()
    if not sys.stdin.isatty():
        return sys.stdin.read()
    raise ValueError("Provide a file argument or pipe script via stdin.")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="ServiceNow developer helper for queries, templates, linting, and skill validation.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  %(prog)s query "find all active incidents assigned to me"
  %(prog)s query "find all incidents assigned to group Bob's Team"
  %(prog)s template scripted-rest-api --table incident
  %(prog)s template flow-script-action --table incident
  %(prog)s template integrationhub-action --table incident
  %(prog)s lint < script.js
  %(prog)s validate-skill /path/to/servicenow""",
    )

    subparsers = parser.add_subparsers(dest="command", help="Command")

    query_parser = subparsers.add_parser("query", help="Generate GlideRecord or GlideAggregate code from natural language.")
    query_parser.add_argument("description", help="Natural language description of the query.")

    tmpl_parser = subparsers.add_parser("template", help="Generate ServiceNow starter templates.")
    tmpl_sub = tmpl_parser.add_subparsers(dest="template_type", help="Template type")

    br_parser = tmpl_sub.add_parser("business-rule", help="Business Rule template")
    br_parser.add_argument("--table", default="incident", help="Table name")
    br_parser.add_argument("--when", choices=["before", "after", "async", "display"], default="before")
    br_parser.add_argument("--insert", action="store_true", help="Fire on insert")
    br_parser.add_argument("--update", action="store_true", help="Fire on update")
    br_parser.add_argument("--delete", action="store_true", help="Fire on delete")
    br_parser.add_argument("--query", action="store_true", help="Fire on query")

    si_parser = tmpl_sub.add_parser("script-include", help="Script Include template")
    si_parser.add_argument("--name", default="MyScriptInclude", help="Class name")
    si_parser.add_argument("--client-callable", action="store_true", help="Generate an AbstractAjaxProcessor-based Script Include")

    cs_parser = tmpl_sub.add_parser("client-script", help="Client Script template")
    cs_parser.add_argument("--type", choices=["onChange", "onLoad", "onSubmit", "onCellEdit"], default="onChange")
    cs_parser.add_argument("--table", default="incident", help="Table name")
    cs_parser.add_argument("--field", default="state", help="Field name for onChange scripts")

    rm_parser = tmpl_sub.add_parser("rest-message", help="Outbound REST Message template")
    rm_parser.add_argument("--method", choices=["GET", "POST", "PUT", "PATCH", "DELETE"], default="GET")
    rm_parser.add_argument("--auth", choices=["basic", "oauth2"], default="oauth2")

    acl_parser = tmpl_sub.add_parser("acl", help="ACL script template")
    acl_parser.add_argument("--table", default="incident", help="Table name")
    acl_parser.add_argument("--type", choices=["record", "field"], default="record")
    acl_parser.add_argument("--operation", choices=["read", "write", "create", "delete"], default="read")

    rest_parser = tmpl_sub.add_parser("scripted-rest-api", help="Scripted REST API resource template")
    rest_parser.add_argument("--table", default="incident", help="Table name")

    flow_parser = tmpl_sub.add_parser("flow-script-action", help="Flow Designer Run Script action template")
    flow_parser.add_argument("--table", default="incident", help="Table name")

    ih_parser = tmpl_sub.add_parser("integrationhub-action", help="IntegrationHub custom action script template")
    ih_parser.add_argument("--table", default="incident", help="Table name for contextual comments")

    atf_parser = tmpl_sub.add_parser("atf-server-test", help="ATF server-side test step template")
    atf_parser.add_argument("--table", default="incident", help="Table name")

    lint_parser = subparsers.add_parser("lint", help="Lint a ServiceNow script for common issues.")
    lint_parser.add_argument("file", nargs="?", help="Path to a script file. If omitted, reads stdin.")

    validate_parser = subparsers.add_parser("validate-skill", help="Validate SKILL.md and bundled references.")
    validate_parser.add_argument("path", nargs="?", default=str(Path(__file__).resolve().parent.parent), help="Path to the skill directory.")

    args = parser.parse_args()

    if args.command == "query":
        print(generate_query(args.description))
        return

    if args.command == "template":
        if args.template_type == "business-rule":
            print(template_business_rule(args))
            return
        if args.template_type == "script-include":
            print(template_script_include(args))
            return
        if args.template_type == "client-script":
            print(template_client_script(args))
            return
        if args.template_type == "rest-message":
            print(template_rest_message(args))
            return
        if args.template_type == "acl":
            print(template_acl(args))
            return
        if args.template_type == "scripted-rest-api":
            print(template_scripted_rest_api(args))
            return
        if args.template_type == "flow-script-action":
            print(template_flow_script_action(args))
            return
        if args.template_type == "integrationhub-action":
            print(template_integrationhub_action(args))
            return
        if args.template_type == "atf-server-test":
            print(template_atf_server_test(args))
            return
        tmpl_parser.print_help()
        return

    if args.command == "lint":
        try:
            script = _read_script_argument(args.file)
        except ValueError as exc:
            print(f"Error: {exc}")
            print("  snow_helper.py lint script.js")
            print("  cat script.js | snow_helper.py lint")
            sys.exit(1)
        print(format_lint_results(lint_script(script)))
        return

    if args.command == "validate-skill":
        errors = validate_skill(args.path)
        if errors:
            print("Skill validation failed:")
            for error in errors:
                print(f"  - {error}")
            sys.exit(1)
        print("✅ Skill validation passed.")
        return

    parser.print_help()


if __name__ == "__main__":
    main()
