#!/usr/bin/env python3
"""Exchange a SimpleFIN setup token for a permanent access URL."""
import argparse
import base64
import binascii
import sys
from pathlib import Path
import requests
from urllib.parse import urlparse

from ledger_one.simplefin import _validate_simplefin_url


def _redact(url: str) -> str:
    p = urlparse(url)
    if p.username or p.password:
        host = p.hostname or ""
        if p.port:
            host += f":{p.port}"
        return f"{p.scheme}://***:***@{host}{p.path}"
    return url


def _decode_claim_url(setup_token: str) -> str:
    try:
        claim_url = base64.b64decode(setup_token.strip(), validate=True).decode("ascii")
    except (binascii.Error, UnicodeDecodeError) as exc:
        raise ValueError("Setup token is not valid base64 ASCII") from exc
    _validate_simplefin_url(claim_url, field_name="SimpleFIN claim URL")
    return claim_url


def _upsert_env_var(path: Path, name: str, value: str) -> None:
    replacement = f"{name}={value}"
    lines = path.read_text().splitlines() if path.exists() else []
    out: list[str] = []
    replaced = False

    for line in lines:
        if line.startswith(f"{name}=") or line.startswith(f"export {name}="):
            out.append(replacement)
            replaced = True
        else:
            out.append(line)

    if not replaced:
        if out and out[-1] != "":
            out.append("")
        out.append(replacement)

    path.write_text("\n".join(out) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("setup_token")
    parser.add_argument(
        "--env-file",
        type=Path,
        default=Path(".env"),
        help="Write SIMPLEFIN_ACCESS_URL to this env file instead of printing it.",
    )
    parser.add_argument(
        "--show-secret",
        action="store_true",
        help="Also print the permanent access URL after saving it.",
    )
    args = parser.parse_args()

    try:
        claim_url = _decode_claim_url(args.setup_token)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    print("Claiming token with SimpleFIN...")
    try:
        resp = requests.post(claim_url, timeout=60)
        resp.raise_for_status()
    except requests.HTTPError as exc:
        status_code = exc.response.status_code if exc.response is not None else None
        if status_code == 403:
            print("Error: this setup token has already been claimed.", file=sys.stderr)
            print("Generate a new one from the SimpleFIN Bridge dashboard.", file=sys.stderr)
        else:
            print(f"Error: SimpleFIN returned HTTP {status_code or 'unknown'}.", file=sys.stderr)
        return 1
    except requests.RequestException as exc:
        print(f"Error contacting SimpleFIN: {exc.__class__.__name__}.", file=sys.stderr)
        return 1
    access_url = resp.text.strip()
    _validate_simplefin_url(access_url, field_name="SimpleFIN access URL")
    _upsert_env_var(args.env_file, "SIMPLEFIN_ACCESS_URL", access_url)
    print(f"\nSaved SIMPLEFIN_ACCESS_URL to {args.env_file} ({_redact(access_url)}).")
    if args.show_secret:
        print(access_url)
    else:
        print("Secret not printed. Re-run with --show-secret if you need to inspect it.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
