#!/usr/bin/env python3
"""
Fulcra OAuth2 Authorization & Token Management

Handles the full token lifecycle:
  1. Device flow authorization (one-time, requires human approval)
  2. Token refresh (automatic, no human needed)
  3. Token status check

Stores both access_token and refresh_token so tokens can be
refreshed indefinitely without re-authorization.

Usage:
    python3 fulcra_auth.py authorize   # First-time setup (interactive)
    python3 fulcra_auth.py refresh     # Refresh access token (automatic)
    python3 fulcra_auth.py status      # Check token status
    python3 fulcra_auth.py token       # Print current access token (for piping)
"""

import http.client
import urllib.parse
import json
import os
import sys
import time
import datetime

# Auth0 config (same as fulcra-api Python client)
AUTH0_DOMAIN = "fulcra.us.auth0.com"
AUTH0_CLIENT_ID = "48p3VbMnr5kMuJAUe9gJ9vjmdWLdnqZt"
AUTH0_AUDIENCE = "https://api.fulcradynamics.com/"
AUTH0_SCOPE = "openid profile email offline_access"

TOKEN_DIR = os.path.expanduser("~/.config/fulcra")
TOKEN_FILE = os.path.join(TOKEN_DIR, "token.json")


def _auth0_post(path, body_dict):
    """POST to Auth0 and return parsed JSON."""
    conn = http.client.HTTPSConnection(AUTH0_DOMAIN)
    body = urllib.parse.urlencode(body_dict)
    headers = {"Content-Type": "application/x-www-form-urlencoded"}
    conn.request("POST", path, body, headers)
    resp = conn.getresponse()
    data = json.loads(resp.read())
    return resp.status, data


def load_token():
    """Load saved token data, or return None."""
    if not os.path.exists(TOKEN_FILE):
        return None
    with open(TOKEN_FILE) as f:
        return json.load(f)


def extract_user_id_from_jwt(access_token):
    """Extract user_id (sub claim) from JWT access token."""
    import base64
    try:
        encoded = access_token.split('.')[1]
        # Add padding
        padding = 4 - len(encoded) % 4
        if padding != 4:
            encoded += '=' * padding
        payload = json.loads(base64.urlsafe_b64decode(encoded))
        return payload.get("sub")
    except Exception:
        return None


def save_token(token_data):
    """Save token data to disk."""
    os.makedirs(TOKEN_DIR, exist_ok=True)
    token_data["saved_at"] = datetime.datetime.now().isoformat()
    
    # Always ensure user_id is present by extracting from JWT
    if not token_data.get("user_id") and token_data.get("access_token"):
        user_id = extract_user_id_from_jwt(token_data["access_token"])
        if user_id:
            token_data["user_id"] = user_id
    
    with open(TOKEN_FILE, "w") as f:
        json.dump(token_data, f, indent=2)
    # Restrict permissions
    os.chmod(TOKEN_FILE, 0o600)


def token_is_valid(token_data):
    """Check if access token is still valid (with 5 min buffer)."""
    if not token_data or "expiration" not in token_data:
        return False
    exp = datetime.datetime.fromisoformat(token_data["expiration"])
    return datetime.datetime.now() < exp - datetime.timedelta(minutes=5)


def token_needs_refresh(token_data):
    """Check if token should be refreshed (within 1 hour of expiry)."""
    if not token_data or "expiration" not in token_data:
        return True
    exp = datetime.datetime.fromisoformat(token_data["expiration"])
    return datetime.datetime.now() > exp - datetime.timedelta(hours=1)


def authorize():
    """Run device flow authorization. Requires human interaction."""
    print("🔐 Fulcra Authorization — Device Flow")
    print("=" * 45)

    # Request device code
    status, data = _auth0_post("/oauth/device/code", {
        "client_id": AUTH0_CLIENT_ID,
        "audience": AUTH0_AUDIENCE,
        "scope": AUTH0_SCOPE,
    })

    if status != 200:
        print(f"❌ Failed to get device code: {data}")
        sys.exit(1)

    device_code = data["device_code"]
    user_code = data["user_code"]
    verification_url = data["verification_uri_complete"]
    interval = data.get("interval", 5)
    expires_in = data.get("expires_in", 900)

    print()
    print(f"👉 Visit: {verification_url}")
    print(f"   Code:  {user_code}")
    print()
    print("Waiting for authorization...")

    # Poll for token
    deadline = time.time() + expires_in
    while time.time() < deadline:
        time.sleep(interval)

        status, data = _auth0_post("/oauth/token", {
            "client_id": AUTH0_CLIENT_ID,
            "grant_type": "urn:ietf:params:oauth:grant-type:device_code",
            "device_code": device_code,
        })

        if status == 200 and "access_token" in data:
            expires_at = datetime.datetime.now() + datetime.timedelta(
                seconds=float(data["expires_in"])
            )
            token_data = {
                "access_token": data["access_token"],
                "refresh_token": data.get("refresh_token"),
                "expiration": expires_at.isoformat(),
                "token_type": data.get("token_type", "Bearer"),
            }

            # Get user ID
            try:
                conn = http.client.HTTPSConnection("api.fulcradynamics.com")
                conn.request("GET", "/data/v0/userid", headers={
                    "Authorization": f"Bearer {token_data['access_token']}"
                })
                resp = conn.getresponse()
                if resp.status == 200:
                    uid_data = json.loads(resp.read())
                    token_data["user_id"] = uid_data.get("user_id") or uid_data.get("userid")
            except Exception:
                pass

            save_token(token_data)

            print()
            print(f"✅ Authorized!")
            print(f"   Token expires: {expires_at.strftime('%Y-%m-%d %H:%M')}")
            print(f"   Refresh token: {'✅ saved' if token_data.get('refresh_token') else '❌ not returned'}")
            if token_data.get("user_id"):
                print(f"   User ID: {token_data['user_id']}")
            print(f"   Saved to: {TOKEN_FILE}")

            if not token_data.get("refresh_token"):
                print()
                print("⚠️  No refresh token returned. Token will expire and need re-auth.")
                print("   This can happen if offline_access wasn't granted.")
            return token_data

        # Check for terminal errors
        error = data.get("error", "")
        if error == "authorization_pending" or error == "slow_down":
            if error == "slow_down":
                interval += 2
            continue
        elif error == "expired_token":
            print("❌ Device code expired. Please try again.")
            sys.exit(1)
        elif error == "access_denied":
            print("❌ Authorization denied.")
            sys.exit(1)
        else:
            print(f"❌ Unexpected error: {data}")
            sys.exit(1)

    print("❌ Timed out waiting for authorization.")
    sys.exit(1)


def refresh():
    """Refresh the access token using the saved refresh token."""
    token_data = load_token()

    if not token_data:
        print("❌ No token file found. Run 'authorize' first.")
        sys.exit(1)

    if not token_data.get("refresh_token"):
        print("❌ No refresh token saved. Run 'authorize' to get one.")
        sys.exit(1)

    if not token_needs_refresh(token_data):
        print(f"✅ Token still fresh (expires {token_data['expiration']})")
        return token_data

    status, data = _auth0_post("/oauth/token", {
        "client_id": AUTH0_CLIENT_ID,
        "grant_type": "refresh_token",
        "refresh_token": token_data["refresh_token"],
    })

    if status != 200 or "access_token" not in data:
        error = data.get("error_description", data.get("error", "unknown"))
        print(f"❌ Refresh failed: {error}")
        print("   You may need to re-authorize: python3 fulcra_auth.py authorize")
        sys.exit(1)

    expires_at = datetime.datetime.now() + datetime.timedelta(
        seconds=float(data["expires_in"])
    )

    # Update token data, preserving user_id and updating refresh_token if rotated
    token_data["access_token"] = data["access_token"]
    token_data["expiration"] = expires_at.isoformat()
    if data.get("refresh_token"):
        token_data["refresh_token"] = data["refresh_token"]

    save_token(token_data)

    print(f"✅ Token refreshed! Expires: {expires_at.strftime('%Y-%m-%d %H:%M')}")
    return token_data


def status():
    """Print token status."""
    token_data = load_token()

    if not token_data:
        print("❌ No token found. Run: python3 fulcra_auth.py authorize")
        return

    has_access = bool(token_data.get("access_token"))
    has_refresh = bool(token_data.get("refresh_token"))
    is_valid = token_is_valid(token_data)
    exp = token_data.get("expiration", "unknown")

    print(f"Access token:  {'✅' if has_access else '❌'}")
    print(f"Refresh token: {'✅' if has_refresh else '❌'}")
    print(f"Valid:         {'✅' if is_valid else '❌ expired'}")
    print(f"Expires:       {exp}")
    if token_data.get("user_id"):
        print(f"User ID:       {token_data['user_id']}")
    if token_data.get("saved_at"):
        print(f"Last saved:    {token_data['saved_at']}")

    if not has_refresh:
        print()
        print("⚠️  No refresh token. Re-run 'authorize' to get one.")
    elif not is_valid:
        print()
        print("Token expired. Run: python3 fulcra_auth.py refresh")


def print_token():
    """Print just the access token (for shell piping / env vars)."""
    token_data = load_token()
    if not token_data or not token_data.get("access_token"):
        sys.exit(1)

    # Auto-refresh if needed and possible
    if not token_is_valid(token_data) and token_data.get("refresh_token"):
        token_data = refresh()

    if token_is_valid(token_data):
        print(token_data["access_token"], end="")
    else:
        sys.exit(1)


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "status"

    if cmd == "authorize":
        authorize()
    elif cmd == "refresh":
        refresh()
    elif cmd == "status":
        status()
    elif cmd == "token":
        print_token()
    else:
        print(f"Unknown command: {cmd}")
        print("Usage: fulcra_auth.py [authorize|refresh|status|token]")
        sys.exit(1)
