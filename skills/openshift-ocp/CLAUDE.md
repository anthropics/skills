# OCP MCP Skills — Claude Code Project

## Overview
This project provides OpenShift automation tools via MCP (Model Context Protocol).
All tools are available through the `ocp-mcp` MCP server defined in `.mcp.json`.

## Skills Available

| Skill | Tools | Purpose |
|---|---|---|
| login_status | check_login, ocp_login | OCP authentication |
| pod_status | get_pods, get_nodes, get_cluster_operators, get_cluster_version | Cluster health |
| nginx_deploy | deploy_nginx, get_nginx_route | App deployment |

## How to Use

Just describe what you want in plain English:
- "Check if I am logged into OCP"
- "Login to my cluster at https://api.cluster.example.com"
- "Show me all pods in namespace monitoring"
- "Are all cluster operators healthy?"
- "What OCP version is running?"
- "Deploy nginx in the dev namespace"

## MCP Server
Entry point: `ocp_mcp_server.py`
Started automatically by Claude Code via `.mcp.json`

## Skill Files
Each skill has a SKILL.md describing its purpose and tools.
See `.claude/skills/` directory.

