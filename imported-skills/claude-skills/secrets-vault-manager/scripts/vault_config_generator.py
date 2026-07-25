#!/usr/bin/env python3
"""Generate Vault policy and auth configuration from application requirements.

Produces HCL policy files and auth method setup commands for HashiCorp Vault
based on application name, auth method, and required secret paths.

Usage:
    python vault_config_generator.py --app-name payment-service --auth-method approle --secrets "db-creds,api-key,tls-cert"
    python vault_config_generator.py --app-name api-gateway --auth-method kubernetes --secrets "db-creds" --namespace production --json
"""

import argparse
import json
import sys
import textwrap
from datetime import datetime


# Default TTLs by auth method
AUTH_METHOD_DEFAULTS = {
    "approle": {
        "token_ttl": "1h",
        "token_max_ttl": "4h",
        "secret_id_num_uses": 1,
        "secret_id_ttl": "10m",
    },
    "kubernetes": {
        "token_ttl": "1h",
        "token_max_ttl": "4h",
    },
    "oidc": {
        "token_ttl": "8h",
        "token_max_ttl": "12h",
    },
}

# Secret type templates
SECRET_TYPE_MAP = {
    "db-creds": {
        "engine": "database",
        "path": "database/creds/{app}-readonly",
        "capabilities": ["read"],
        "description": "Dynamic database credentials",
    },
    "db-admin": {
        "engine": "database",
        "path": "database/creds/{app}-readwrite",
        "capabilities": ["read"],
        "description": "Dynamic database admin credentials",
    },
    "api-key": {
        "engine": "kv-v2",
        "path": "secret/data/{env}/{app}/api-keys",
        "capabilities": ["read"],
        "description": "Static API keys (KV v2)",
    },
    "tls-cert": {
        "engine": "pki",
        "path": "pki/issue/{app}-cert",
        "capabilities": ["create", "update"],
        "description": "TLS certificate issuance",
    },
    "encryption": {
        "engine": "transit",
        "path": "transit/encrypt/{app}-key",
        "capabilities": ["update"],
        "description": "Transit encryption operations",
    },
    "ssh-cert": {
        "engine": "ssh",
        "path": "ssh/sign/{app}-role",
        "capabilities": ["create", "update"],
        "description": "SSH certificate signing",
    },
    "config": {
        "engine": "kv-v2",
        "path": "secret/data/{env}/{app}/config",
        "capabilities": ["read"],
        "description": "Application configuration secrets",
    },
}


def parse_secrets(secrets_str):
    """Parse comma-separated secret types into list."""
    secrets = [s.strip() for s in secrets_str.split(",") if s.strip()]
    valid = []
    unknown = []
    for s in secrets:
        if s in SECRET_TYPE_MAP:
            valid.append(s)
        else:
            unknown.append(s)
    return valid, unknown


def generate_policy_hcl(app_name, secrets, environment="production"):
    """Generate HCL policy document."""
    lines = [
        f'# Vault policy for {app_name}',
        f'# Generated: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}',
        f'# Environment: {environment}',
        '',
    ]

    for secret_type in secrets:
        tmpl = SECRET_TYPE_MAP[secret_type]
        path = tmpl["path"].format(app=app_name, env=environment)
        caps = ", ".join(f'"{c}"' for c in tmpl["capabilities"])

        lines.append(f'# {tmpl["description"]}')
        lines.append(f'path "{path}" {{')
        lines.append(f'  capabilities = [{caps}]')
        lines.append('}')
        lines.append('')

    # Always deny sys paths
    lines.append('# Deny admin paths')
    lines.append('path "sys/*" {')
    lines.append('  capabilities = ["deny"]')
    lines.append('}')

    return "\n".join(lines)


def generate_auth_config(app_name, auth_method, policy_name, namespace=None):
    """Generate auth method setup commands."""
    commands = []
    defaults = AUTH_METHOD_DEFAULTS.get(auth_method, {})

    if auth_method == "approle":
        cmd = (
            f"vault write auth/approle/role/{app_name} \\\n"
            f"  token_ttl={defaults['token_ttl']} \\\n"
            f"  token_max_ttl={defaults['token_max_ttl']} \\\n"
            f"  secret_id_num_uses={defaults['secret_id_num_uses']} \\\n"
            f"  secret_id_ttl={defaults['secret_id_ttl']} \\\n"
            f"  token_policies=\"{policy_name}\""
        )
        commands.append({"description": f"Create AppRole for {app_name}", "command": cmd})

        commands.append({
            "description": "Fetch RoleID",
            "command": f"vault read auth/approle/role/{app_name}/role-id",
        })
        commands.append({
            "description": "Generate SecretID (single-use)",
            "command": f"vault write -f auth/approle/role/{app_name}/secret-id",
        })

    elif auth_method == "kubernetes":
        ns = namespace or "default"
        cmd = (
            f"vault write auth/kubernetes/role/{app_name} \\\n"
            f"  bound_service_account_names={app_name} \\\n"
            f"  bound_service_account_namespaces={ns} \\\n"
            f"  policies={policy_name} \\\n"
            f"  ttl={defaults['token_ttl']}"
        )
        commands.append({"description": f"Create Kubernetes auth role for {app_name}", "command": cmd})

    elif auth_method == "oidc":
        cmd = (
            f"vault write auth/oidc/role/{app_name} \\\n"
            f"  bound_audiences=\"vault\" \\\n"
            f"  allowed_redirect_uris=\"https://vault.example.com/ui/vault/auth/oidc/oidc/callback\" \\\n"
            f"  user_claim=\"email\" \\\n"
            f"  oidc_scopes=\"openid,profile,email\" \\\n"
            f"  policies=\"{policy_name}\" \\\n"
            f"  ttl={defaults['token_ttl']}"
        )
        commands.append({"description": f"Create OIDC role for {app_name}", "command": cmd})

    return commands


def build_output(app_name, auth_method, secrets, environment, namespace):
    """Build complete configuration output."""
    valid_secrets, unknown_secrets = parse_secrets(secrets)

    if not valid_secrets:
        return {
            "error": "No valid secret types provided",
            "unknown": unknown_secrets,
            "available_types": list(SECRET_TYPE_MAP.keys()),
        }

    policy_name = f"{app_name}-policy"
    policy_hcl = generate_policy_hcl(app_name, valid_secrets, environment)
    auth_commands = generate_auth_config(app_name, auth_method, policy_name, namespace)

    secret_details = []
    for s in valid_secrets:
        tmpl = SECRET_TYPE_MAP[s]
        secret_details.append({
            "type": s,
            "engine": tmpl["engine"],
            "path": tmpl["path"].format(app=app_name, env=environment),
            "capabilities": tmpl["capabilities"],
            "description": tmpl["description"],
        })

    result = {
        "app_name": app_name,
        "auth_method": auth_method,
        "environment": environment,
        "policy_name": policy_name,
        "policy_hcl": policy_hcl,
        "auth_commands": auth_commands,
        "secrets": secret_details,
        "generated_at": datetime.now().isoformat(),
    }

    if unknown_secrets:
        result["warnings"] = [f"Unknown secret type '{u}' — skipped. Available: {list(SECRET_TYPE_MAP.keys())}" for u in unknown_secrets]
    if namespace:
        result["namespace"] = namespace

    return result


def print_human(result):
    """Print human-readable output."""
    if "error" in result:
        print(f"ERROR: {result['error']}")
        if result.get("unknown"):
            print(f"  Unknown types: {', '.join(result['unknown'])}")
        print(f"  Available types: {', '.join(result['available_types'])}")
        sys.exit(1)

    print(f"=== Vault Configuration for {result['app_name']} ===")
    print(f"Auth Method: {result['auth_method']}")
    print(f"Environment: {result['environment']}")
    print(f"Policy Name: {result['policy_name']}")
    print()

    if result.get("warnings"):
        for w in result["warnings"]:
            print(f"WARNING: {w}")
        print()

    print("--- Policy HCL ---")
    print(result["policy_hcl"])
    print()

    print(f"Write policy: vault policy write {result['policy_name']} {result['policy_name']}.hcl")
    print()

    print("--- Auth Method Setup ---")
    for cmd_info in result["auth_commands"]:
        print(f"# {cmd_info['description']}")
        print(cmd_info["command"])
        print()

    print("--- Secret Paths ---")
    for s in result["secrets"]:
        caps = ", ".join(s["capabilities"])
        print(f"  {s['type']:15s}  {s['path']:50s}  [{caps}]")


def main():
    parser = argparse.ArgumentParser(
        description="Generate Vault policy and auth configuration from application requirements.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=textwrap.dedent("""\
            Secret types:
              db-creds     Dynamic database credentials (read-only)
              db-admin     Dynamic database credentials (read-write)
              api-key      Static API keys in KV v2
              tls-cert     TLS certificate issuance via PKI
              encryption   Transit encryption-as-a-service
              ssh-cert     SSH certificate signing
              config       Application configuration secrets

            Examples:
              %(prog)s --app-name payment-svc --auth-method approle --secrets "db-creds,api-key"
              %(prog)s --app-name api-gw --auth-method kubernetes --secrets "db-creds,config" --namespace prod --json
        """),
    )
    parser.add_argument("--app-name", required=True, help="Application or service name")
    parser.add_argument(
        "--auth-method",
        required=True,
        choices=["approle", "kubernetes", "oidc"],
        help="Vault auth method to configure",
    )
    parser.add_argument("--secrets", required=True, help="Comma-separated secret types (e.g., db-creds,api-key,tls-cert)")
    parser.add_argument("--environment", default="production", help="Target environment (default: production)")
    parser.add_argument("--namespace", help="Kubernetes namespace (for kubernetes auth method)")
    parser.add_argument("--json", action="store_true", dest="json_output", help="Output as JSON")

    args = parser.parse_args()
    result = build_output(args.app_name, args.auth_method, args.secrets, args.environment, args.namespace)

    if args.json_output:
        print(json.dumps(result, indent=2))
    else:
        print_human(result)


if __name__ == "__main__":
    main()
