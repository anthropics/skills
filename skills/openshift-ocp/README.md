# OCP Claude Skills

> **First OpenShift skill in the Claude ecosystem** — OpenShift cluster automation via FastMCP + Claude Code.

[![FastMCP](https://img.shields.io/badge/FastMCP-3.2.4-blue)](https://gofastmcp.com)
[![OCP](https://img.shields.io/badge/OpenShift-4.18%2B-red)](https://www.redhat.com/en/technologies/cloud-computing/openshift)
[![Claude Code](https://img.shields.io/badge/Claude%20Code-Compatible-green)](https://code.claude.com)
[![License](https://img.shields.io/badge/License-Apache%202.0-yellow)](LICENSE)

---

## What It Does

Natural language OpenShift cluster management through Claude Code.
Just describe what you want — Claude calls the right tool automatically.

```
"Am I logged into OCP?"
"Show me all nodes"
"Are all cluster operators healthy?"
"Show pods in namespace openshift-monitoring"
"What OCP version is running?"
```

---

## Current Scope

This skill focuses on **OpenShift cluster management** — login, node health, pod status, and cluster operator monitoring. All tools below marked ✓ are fully tested against a live OCP 4.14 cluster.

> **Note:** The `nginx_deploy` skill is included in the codebase as a contribution template but has **not been fully tested**.
> Community contributions to extend, test, or improve it are very welcome — see the Contributing section below.

---

## Architecture

```
You (natural language)
        ↓
Claude Code reads CLAUDE.md + SKILL.md
        ↓
Claude calls MCP tool via .mcp.json
        ↓
FastMCP server (ocp_mcp_server.py) executes oc command
        ↓
Result returned and analyzed by Claude
```

**SKILL.md** → Tells Claude *when* to use which tool  
**FastMCP**  → Executes the actual `oc` commands  
**MCP**      → The protocol connecting Claude Code to the server

---

## Skills & Tools

| Skill | Tool | Status | Description |
|---|---|---|---|
| login_status | `check_login` | ✓ Tested | Show current user and server URL |
| login_status | `ocp_login` | ✓ Tested | Login to an OCP cluster |
| pod_status | `get_pods` | ✓ Tested | Get all pods in a namespace |
| pod_status | `get_nodes` | ✓ Tested | Get all nodes and status |
| pod_status | `get_cluster_operators` | ✓ Tested | Check all cluster operators |
| pod_status | `get_cluster_version` | ✓ Tested | Get OCP version |
| nginx_deploy | `deploy_nginx` | ⚠ Contribution Welcome | Deploy nginx using UBI image |
| nginx_deploy | `get_nginx_route` | ⚠ Contribution Welcome | Get exposed route URL |

---

## Requirements

- Claude Code installed
- `oc` CLI installed and in PATH
- Python 3.8+ (tested on Python 3.12 / RHEL9)
- Active OCP cluster (tested on OCP 4.18 / Kubernetes v1.31)
- `pip install fastmcp`

---

## Installation

```bash
# Clone the repo
git clone https://github.com/ibanerjeedoc21-source/ocp-claude-skills
cd ocp-claude-skills

# Install dependency
pip3 install fastmcp

# On RHEL9 with multiple Python versions:
python3.12 -m pip install fastmcp

# Verify
python3.12 -c "import fastmcp; print('fastmcp OK')"

# Verify oc is working
oc whoami

# Start Claude Code — MCP server starts automatically
claude
```

---

## Verify MCP Connected

Inside Claude Code:
```
/mcp
```

Expected output:
```
ocp-mcp · ✓ connected
  /ocp-mcp:pod_health_prompt
  /ocp-mcp:login_status_prompt
  /ocp-mcp:nginx_deploy_prompt
```

---

## Demo Output

### Get Nodes
```
6 nodes — 3 masters + 3 workers — all Ready

vmocp-master1   control-plane   10.254.x.x   v1.31.11
vmocp-master2   control-plane   10.254.x.x   v1.31.11
vmocp-master3   control-plane   10.254.x.x   v1.31.11
vmocp-worker1   worker          10.254.x.x   v1.31.11
vmocp-worker2   worker          10.254.x.x   v1.31.11
vmocp-worker3   worker          10.254.x.x   v1.31.11
```

### Get Pods (openshift-monitoring)
```
23 pods — all Running

alertmanager-main-0                   6/6    Running
alertmanager-main-1                   6/6    Running
cluster-monitoring-operator-*         1/1    Running
kube-state-metrics-*                  3/3    Running
prometheus-k8s-0                      6/6    Running
prometheus-k8s-1                      6/6    Running
thanos-querier-*                      6/6    Running
... (23 total)
```

---

## Project Structure

```
ocp-claude-skills/
├── CLAUDE.md                        ← Claude Code project instructions
├── .mcp.json                        ← MCP client config (auto-starts server)
├── ocp_mcp_server.py                ← FastMCP server (all tools)
├── requirements.txt                 ← fastmcp
├── MOP.txt                          ← Minimum Operating Procedure / runbook
├── demo-screenshot/                 ← Live test screenshots
└── .claude/
    └── skills/
        ├── login_status/SKILL.md    ← Login skill instructions
        ├── pod_status/SKILL.md      ← Pod/node/CO skill instructions
        └── nginx_deploy/SKILL.md   ← Nginx deploy (contribution welcome)
```

---

## Tested On

| Component | Version |
|---|---|
| OCP | 4.14 |
| Kubernetes | v1.31.11 |
| FastMCP | 3.2.4 |
| Python | 3.12 |
| OS | RHEL 9 |
| Claude Code | v2.1.112 |

---

## MCP Primitives Used

This skill implements all three MCP primitives:

```
Tools     → oc command execution         (8 tools)
Prompts   → reusable analysis templates  (3 prompts)
Resources → live cluster context         (2 resources)
```

---

## Roadmap

- [ ] `oc describe pod` for deep pod inspection
- [ ] `oc get events` for cluster event analysis
- [ ] `oc logs` streaming via WebSocket transport
- [ ] OpenShift AI / RHOAI namespace monitoring
- [ ] HTTP+SSE transport for remote VM access
- [ ] Test and complete nginx_deploy skill

---

## Contributing

Issues and PRs are welcome!

- To **test and complete** the nginx_deploy skill — see `.claude/skills/nginx_deploy/SKILL.md`
- To **add new OCP tools** — follow the existing pattern in `ocp_mcp_server.py` and add a corresponding SKILL.md
- Please keep tools compatible with both **Claude Code** and **Aider** (use `**Triggers:**` and `**Run:**` annotations in SKILL.md)

---

## Author

**Indranil Banerjee**  
Senior Technical Consultant @ HPE (current) | ex-TCS | ex-Wipro  
OpenShift • DevOps • Multi-Cloud | Building with RAG, Agentic AI & Claude  
NVIDIA + Azure AI Certified | RHCS OpenShift Admin  
18+ years Unix/Linux/DevOps/OCP infrastructure  
📍 Kolkata, West Bengal, India  
[LinkedIn](https://www.linkedin.com/in/indranil-banerjee-894a5016) · [Medium](https://i-banerjee83.medium.com)

