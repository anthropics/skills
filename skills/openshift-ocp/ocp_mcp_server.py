# ocp_mcp_server.py
# Main FastMCP server — registers all OCP skill tools

from fastmcp import FastMCP
import subprocess

mcp = FastMCP("ocp-mcp")

# ─────────────────────────────────────────
# SKILL: login_status
# ─────────────────────────────────────────

@mcp.tool()
def check_login() -> str:
    """Check if currently logged into OCP — returns current user and server"""
    result = subprocess.run(
        ["oc", "whoami", "--show-server"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Not logged in: {result.stderr.strip()}"
    user = subprocess.run(["oc", "whoami"], capture_output=True, text=True)
    return f"User: {user.stdout.strip()}\nServer: {result.stdout.strip()}"


@mcp.tool()
def ocp_login(server: str, username: str, password: str) -> str:
    """Login to an OCP cluster"""
    result = subprocess.run(
        ["oc", "login", server, "-u", username, "-p", password,
         "--insecure-skip-tls-verify=true"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Login failed: {result.stderr.strip()}"
    return f"Login successful:\n{result.stdout.strip()}"


@mcp.prompt()
def login_status_prompt() -> str:
    """Prompt to summarize OCP login and cluster health"""
    return (
        "Check if I am logged into OCP. "
        "Show current user, server URL, and tell me if login is active or expired."
    )


@mcp.resource("ocp://login-status")
def login_status_resource() -> str:
    """Current OCP login status as a resource"""
    result = subprocess.run(["oc", "whoami"], capture_output=True, text=True)
    if result.returncode != 0:
        return "Status: NOT LOGGED IN"
    return f"Status: LOGGED IN\nUser: {result.stdout.strip()}"


# ─────────────────────────────────────────
# SKILL: pod_status
# ─────────────────────────────────────────

@mcp.tool()
def get_pods(namespace: str) -> str:
    """Get all pods and their status in a given namespace"""
    result = subprocess.run(
        ["oc", "get", "pods", "-n", namespace, "-o", "wide"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Error: {result.stderr.strip()}"
    return result.stdout


@mcp.tool()
def get_nodes() -> str:
    """Get all OCP nodes and their status"""
    result = subprocess.run(
        ["oc", "get", "nodes", "-o", "wide"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Error: {result.stderr.strip()}"
    return result.stdout


@mcp.tool()
def get_cluster_operators() -> str:
    """Get all cluster operators and their availability status"""
    result = subprocess.run(
        ["oc", "get", "co"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Error: {result.stderr.strip()}"
    return result.stdout


@mcp.tool()
def get_cluster_version() -> str:
    """Get current OCP cluster version"""
    result = subprocess.run(
        ["oc", "get", "clusterversion"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Error: {result.stderr.strip()}"
    return result.stdout


@mcp.prompt()
def pod_health_prompt(namespace: str) -> str:
    """Prompt to analyze pod health in a namespace"""
    return (
        f"Get all pods in namespace '{namespace}'. "
        f"Identify any pods that are NOT in Running or Completed state. "
        f"For each unhealthy pod, tell me the status and likely cause."
    )


@mcp.resource("ocp://cluster-overview")
def cluster_overview_resource() -> str:
    """Quick cluster overview — version and node count"""
    version = subprocess.run(
        ["oc", "get", "clusterversion", "-o", "jsonpath={.items[0].status.desired.version}"],
        capture_output=True, text=True
    )
    nodes = subprocess.run(
        ["oc", "get", "nodes", "--no-headers"],
        capture_output=True, text=True
    )
    node_count = len(nodes.stdout.strip().splitlines()) if nodes.returncode == 0 else "unknown"
    return f"OCP Version: {version.stdout.strip()}\nTotal Nodes: {node_count}"


# ─────────────────────────────────────────
# SKILL: nginx_deploy
# ─────────────────────────────────────────

@mcp.tool()
def deploy_nginx(namespace: str, app_name: str = "nginx-app") -> str:
    """Deploy nginx using UBI image on OCP in a given namespace"""
    cmds = [
        ["oc", "new-app", "registry.access.redhat.com/ubi8/nginx-120",
         "--name", app_name, "-n", namespace],
        ["oc", "expose", "svc", app_name, "-n", namespace],
    ]
    output = []
    for cmd in cmds:
        result = subprocess.run(cmd, capture_output=True, text=True)
        output.append(result.stdout if result.returncode == 0 else result.stderr)
    return "\n".join(output)


@mcp.tool()
def get_nginx_route(namespace: str, app_name: str = "nginx-app") -> str:
    """Get the exposed route URL for nginx deployment"""
    result = subprocess.run(
        ["oc", "get", "route", app_name, "-n", namespace,
         "-o", "jsonpath={.spec.host}"],
        capture_output=True, text=True
    )
    if result.returncode != 0:
        return f"Error: {result.stderr.strip()}"
    return f"Route URL: http://{result.stdout.strip()}"


@mcp.prompt()
def nginx_deploy_prompt(namespace: str) -> str:
    """Prompt to deploy and verify nginx on OCP"""
    return (
        f"Deploy nginx in namespace '{namespace}' using UBI image. "
        f"After deployment, check pod status and get the route URL. "
        f"Tell me if the deployment was successful."
    )


# ─────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────

if __name__ == "__main__":
    mcp.run()

