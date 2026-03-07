#!/usr/bin/env python3
"""x402-client CLI: BRC-31 authentication + BRC-29 payment client."""
import sys
import os

# Ensure lib/ imports work regardless of cwd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import argparse
import json
import logging
import time

from lib.handshake import do_handshake, get_or_create_session, HandshakeError
from lib.auth_request import authenticated_request, AuthRequestError
from lib.session import load_session, clear_session, clear_all_sessions, Session
from lib.metanet import get_identity_key, MetaNetClientError
from lib import registry

# payment.py may not exist yet (built in parallel); import conditionally.
try:
    from lib.payment import paid_request, PaymentError, PaymentRequired
    HAS_PAYMENT = True
except ImportError:
    HAS_PAYMENT = False

log = logging.getLogger("x402-client")


# ---------------------------------------------------------------------------
# Terminal colors (best-effort, no hard dependency)
# ---------------------------------------------------------------------------

class _Colors:
    """ANSI colors, disabled if not a TTY or NO_COLOR is set."""

    def __init__(self):
        use_color = (
            hasattr(sys.stdout, "isatty")
            and sys.stdout.isatty()
            and os.environ.get("NO_COLOR") is None
            and os.environ.get("TERM") != "dumb"
        )
        if use_color:
            self.BOLD = "\033[1m"
            self.DIM = "\033[2m"
            self.GREEN = "\033[32m"
            self.YELLOW = "\033[33m"
            self.RED = "\033[31m"
            self.CYAN = "\033[36m"
            self.RESET = "\033[0m"
        else:
            self.BOLD = ""
            self.DIM = ""
            self.GREEN = ""
            self.YELLOW = ""
            self.RED = ""
            self.CYAN = ""
            self.RESET = ""


C = _Colors()


# ---------------------------------------------------------------------------
# Output helpers
# ---------------------------------------------------------------------------

def print_err(msg: str):
    """Print an error message to stderr with color."""
    print(f"{C.RED}Error:{C.RESET} {msg}", file=sys.stderr)


def print_header(label: str, value: str):
    """Print a labeled value."""
    print(f"  {C.DIM}{label}:{C.RESET} {value}")


def print_section(title: str):
    """Print a section header."""
    print(f"\n{C.BOLD}{title}{C.RESET}")


def format_age(seconds: float) -> str:
    """Format an age in seconds as a human-readable string."""
    if seconds < 60:
        return f"{seconds:.0f}s"
    elif seconds < 3600:
        return f"{seconds / 60:.1f}m"
    else:
        return f"{seconds / 3600:.1f}h"


def print_session(session: Session):
    """Print session details in a readable format."""
    age = time.time() - session.timestamp
    print_header("Server URL", session.server_url)
    print_header("Server identity key", session.server_identity_key)
    print_header("Server nonce", session.server_nonce_b64)
    print_header("Client nonce", session.client_nonce_b64)
    print_header("Age", format_age(age))
    print_header("Expired", str(session.is_expired()))


def print_response(resp, label: str = "Response"):
    """Print an HTTP response in a clean, readable format."""
    # Status line
    status_color = C.GREEN if resp.status_code < 400 else C.YELLOW if resp.status_code < 500 else C.RED
    print(f"\n{C.BOLD}{label}:{C.RESET} {status_color}{resp.status_code} {resp.reason}{C.RESET}")

    # Auth headers (x-bsv-auth-*)
    auth_hdrs = {k: v for k, v in resp.headers.items() if k.lower().startswith("x-bsv-auth-")}
    if auth_hdrs:
        print_section("Auth headers")
        for k, v in sorted(auth_hdrs.items()):
            print_header(k, v)

    # Payment headers (x-bsv-payment-*)
    pay_hdrs = {k: v for k, v in resp.headers.items() if k.lower().startswith("x-bsv-payment")}
    if pay_hdrs:
        print_section("Payment headers")
        for k, v in sorted(pay_hdrs.items()):
            print_header(k, v)

    # Body
    body = resp.text
    if body:
        print_section("Body")
        # Try to pretty-print JSON
        try:
            parsed = json.loads(body)
            print(json.dumps(parsed, indent=2))
        except (json.JSONDecodeError, ValueError):
            print(body)
    else:
        print_section("Body")
        print("  (empty)")


# ---------------------------------------------------------------------------
# Command handlers
# ---------------------------------------------------------------------------

def cmd_identity(args):
    """Show wallet identity key."""
    try:
        key = get_identity_key()
    except MetaNetClientError as e:
        print_err(str(e))
        print_err(
            "Make sure MetaNet Client is running "
            "(look for the app in /Applications)."
        )
        return 1

    print(key)
    return 0


def cmd_handshake(args):
    """Perform BRC-31 handshake with a server."""
    server_url = args.server_url.rstrip("/")

    print(f"Performing BRC-31 handshake with {C.CYAN}{server_url}{C.RESET}...")
    try:
        session = do_handshake(server_url)
    except HandshakeError as e:
        print_err(str(e))
        return 1
    except MetaNetClientError as e:
        print_err(str(e))
        print_err(
            "Make sure MetaNet Client is running."
        )
        return 1

    print(f"{C.GREEN}Handshake successful.{C.RESET}")
    print_section("Session")
    print_session(session)
    return 0


def cmd_session(args):
    """Show, clear, or clear-all stored sessions."""
    # --clear-all
    if args.clear_all:
        count = clear_all_sessions()
        if count == 0:
            print("No stored sessions to clear.")
        else:
            print(f"Cleared {count} stored session(s).")
        return 0

    # --clear <server_url>
    if args.clear:
        if not args.server_url:
            print_err("--clear requires a server URL argument.")
            return 1
        server_url = args.server_url.rstrip("/")
        deleted = clear_session(server_url)
        if deleted:
            print(f"Cleared session for {server_url}.")
        else:
            print(f"No stored session found for {server_url}.")
        return 0

    # show session
    if not args.server_url:
        print_err("Provide a server URL, or use --clear-all.")
        return 1

    server_url = args.server_url.rstrip("/")
    session = load_session(server_url)
    if session is None:
        print(f"No stored session for {server_url}.")
        print(f"Run: python3 cli.py handshake {server_url}")
        return 1

    print_section("Stored session")
    print_session(session)

    # Also print as JSON for scripting
    print_section("JSON")
    print(json.dumps(session.to_dict(), indent=2))
    return 0


def cmd_list(args):
    """List agents from the x402agency.com registry."""
    try:
        agents = registry.list_agents()
    except Exception as e:
        print_err(f"Could not load agent registry: {e}")
        return 1

    if not agents:
        print("No agents found in registry.")
        return 0

    # Calculate column widths
    name_w = max(len(a.get("name", "")) for a in agents)
    name_w = max(name_w, 4)  # minimum "Name" header width
    tagline_w = max(len(a.get("tagline", "")) for a in agents)
    tagline_w = max(tagline_w, 7)  # minimum "Tagline" header width

    # Print table
    print(f"  {C.BOLD}{'Name':<{name_w}}  {'Tagline':<{tagline_w}}  {'URL'}{C.RESET}")
    print(f"  {'-' * name_w}  {'-' * tagline_w}  {'-' * 40}")
    for a in agents:
        name = a.get("name", "?")
        tagline = a.get("tagline", "")
        url = a.get("url", "")
        print(f"  {C.CYAN}{name:<{name_w}}{C.RESET}  {tagline:<{tagline_w}}  {C.DIM}{url}{C.RESET}")

    return 0


def cmd_auth(args):
    """Make a BRC-31 authenticated request (no payment)."""
    method = args.method.upper()
    url = args.url
    body = args.body

    try:
        url = registry.resolve(url)
    except ValueError as e:
        print_err(str(e))
        return 1

    print(
        f"{C.DIM}BRC-31 auth request:{C.RESET} "
        f"{C.BOLD}{method}{C.RESET} {C.CYAN}{url}{C.RESET}"
    )

    try:
        resp = authenticated_request(
            method=method,
            url=url,
            body=body,
        )
    except AuthRequestError as e:
        print_err(str(e))
        return 1
    except HandshakeError as e:
        print_err(f"Handshake failed: {e}")
        return 1
    except MetaNetClientError as e:
        print_err(str(e))
        print_err("Make sure MetaNet Client is running.")
        return 1

    print_response(resp)

    # Return non-zero for server errors (5xx), but 0 for client errors (4xx)
    # since those are valid protocol responses (e.g. 402 Payment Required).
    if resp.status_code >= 500:
        return 1
    return 0


def cmd_pay(args):
    """Make a BRC-31 auth + BRC-29 payment request."""
    if not HAS_PAYMENT:
        print_err(
            "Payment module not available. "
            "lib/payment.py has not been built yet."
        )
        print_err(
            "Use 'auth' command for authenticated requests without payment, "
            "or wait for payment.py to be completed."
        )
        return 1

    method = args.method.upper()
    url = args.url
    body = args.body

    try:
        url = registry.resolve(url)
    except ValueError as e:
        print_err(str(e))
        return 1

    print(
        f"{C.DIM}BRC-31 auth + BRC-29 payment request:{C.RESET} "
        f"{C.BOLD}{method}{C.RESET} {C.CYAN}{url}{C.RESET}"
    )

    try:
        resp = paid_request(
            method=method,
            url=url,
            body=body,
        )
    except PaymentError as e:
        print_err(f"Payment error: {e}")
        return 1
    except AuthRequestError as e:
        print_err(str(e))
        return 1
    except HandshakeError as e:
        print_err(f"Handshake failed: {e}")
        return 1
    except MetaNetClientError as e:
        print_err(str(e))
        print_err("Make sure MetaNet Client is running.")
        return 1

    print_response(resp)

    if resp.status_code >= 500:
        return 1
    return 0


# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    """Build the CLI argument parser with subcommands."""
    parser = argparse.ArgumentParser(
        prog="x402-client",
        description="BRC-31 authentication + BRC-29 payment client CLI.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""examples:
  python3 cli.py list
  python3 cli.py identity
  python3 cli.py handshake http://localhost:8787
  python3 cli.py session http://localhost:8787
  python3 cli.py session --clear http://localhost:8787
  python3 cli.py session --clear-all
  python3 cli.py auth GET http://localhost:8787/
  python3 cli.py auth POST http://localhost:8787/free
  python3 cli.py auth POST banana/generate          (name-based)
  python3 cli.py pay POST http://localhost:8787/paid
  python3 cli.py pay POST banana/generate '{"prompt":"a cat"}' (name-based)
""",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Enable verbose (DEBUG) logging.",
    )

    subparsers = parser.add_subparsers(
        dest="command",
        title="commands",
        metavar="<command>",
    )

    # --- list ---
    subparsers.add_parser(
        "list",
        help="List agents from the x402agency.com registry.",
    )

    # --- identity ---
    subparsers.add_parser(
        "identity",
        help="Show wallet identity key.",
    )

    # --- handshake ---
    p_hs = subparsers.add_parser(
        "handshake",
        help="Perform BRC-31 handshake with a server.",
    )
    p_hs.add_argument(
        "server_url",
        help="Server base URL (e.g. http://localhost:8787).",
    )

    # --- session ---
    p_sess = subparsers.add_parser(
        "session",
        help="Show or manage stored BRC-31 sessions.",
    )
    p_sess.add_argument(
        "server_url",
        nargs="?",
        default=None,
        help="Server URL to look up.",
    )
    p_sess.add_argument(
        "--clear",
        action="store_true",
        help="Clear stored session for the given server URL.",
    )
    p_sess.add_argument(
        "--clear-all",
        action="store_true",
        help="Clear all stored sessions.",
    )

    # --- auth ---
    p_auth = subparsers.add_parser(
        "auth",
        help="BRC-31 authenticated request (no payment).",
    )
    p_auth.add_argument(
        "method",
        help="HTTP method (GET, POST, PUT, DELETE, etc.).",
    )
    p_auth.add_argument(
        "url",
        help="Full URL to request.",
    )
    p_auth.add_argument(
        "body",
        nargs="?",
        default=None,
        help="Request body (JSON string). Optional.",
    )

    # --- pay ---
    p_pay = subparsers.add_parser(
        "pay",
        help="BRC-31 auth + BRC-29 payment request (handles 402).",
    )
    p_pay.add_argument(
        "method",
        help="HTTP method (GET, POST, PUT, DELETE, etc.).",
    )
    p_pay.add_argument(
        "url",
        help="Full URL to request.",
    )
    p_pay.add_argument(
        "body",
        nargs="?",
        default=None,
        help="Request body (JSON string). Optional.",
    )

    return parser


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    """CLI entry point. Returns exit code."""
    parser = build_parser()
    args = parser.parse_args()

    # --- Logging setup ---
    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(name)s %(levelname)s: %(message)s",
        )
    else:
        logging.basicConfig(
            level=logging.WARNING,
            format="%(message)s",
        )

    # --- Dispatch ---
    if args.command is None:
        parser.print_help()
        return 0

    dispatch = {
        "list": cmd_list,
        "identity": cmd_identity,
        "handshake": cmd_handshake,
        "session": cmd_session,
        "auth": cmd_auth,
        "pay": cmd_pay,
    }

    handler = dispatch.get(args.command)
    if handler is None:
        parser.print_help()
        return 1

    try:
        return handler(args)
    except KeyboardInterrupt:
        print("\nInterrupted.", file=sys.stderr)
        return 130
    except Exception as e:
        # Catch-all for unexpected errors
        log.debug("Unexpected error", exc_info=True)
        print_err(f"Unexpected error: {e}")
        if args.verbose:
            import traceback
            traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
