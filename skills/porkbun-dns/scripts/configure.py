#!/usr/bin/env python3
"""
Configure Porkbun API credentials.

Usage:
    python configure.py                         # Interactive setup
    python configure.py --test                  # Test current credentials
"""

import argparse
import json
import os
import sys
import stat

CONFIG_DIR = os.path.expanduser("~/.config/porkbun-cli")
CONFIG_FILE = os.path.join(CONFIG_DIR, "config.json")

def load_config():
    """Load existing config."""
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE) as f:
            return json.load(f)
    return {}

def save_config(config):
    """Save config file with secure permissions."""
    os.makedirs(CONFIG_DIR, exist_ok=True)
    with open(CONFIG_FILE, 'w') as f:
        json.dump(config, f, indent=2)
    # Set file permissions to 600 (owner read/write only)
    os.chmod(CONFIG_FILE, stat.S_IRUSR | stat.S_IWUSR)
    print(f"Configuration saved to {CONFIG_FILE}")

def test_credentials():
    """Test API credentials."""
    try:
        import requests
    except ImportError:
        print("Error: requests library required: pip install requests")
        return False

    config = load_config()
    if not config.get("apikey") or not config.get("secretapikey"):
        # Try environment variables
        config = {
            "apikey": os.environ.get("PORKBUN_API_KEY"),
            "secretapikey": os.environ.get("PORKBUN_SECRET_KEY")
        }
        if not config.get("apikey"):
            print("No credentials found. Run configure.py to set up.")
            return False

    url = "https://api.porkbun.com/api/json/v3/ping"
    try:
        response = requests.post(url, json=config)
        result = response.json()
        if result.get("status") == "SUCCESS":
            print(f"API connection successful!")
            print(f"Your IP: {result.get('yourIp', 'unknown')}")
            return True
        else:
            print(f"API error: {result.get('message', 'Unknown error')}")
            return False
    except Exception as e:
        print(f"Connection error: {e}")
        return False

def interactive_setup():
    """Interactive credential setup."""
    print("Porkbun API Configuration")
    print("-" * 40)
    print("\nTo get API credentials:")
    print("1. Log into https://porkbun.com")
    print("2. Go to Account → API Access")
    print("3. Click 'Create API Key'")
    print()

    current = load_config()

    api_key = input(f"API Key [{current.get('apikey', '')[:8] + '...' if current.get('apikey') else 'not set'}]: ").strip()
    if not api_key and current.get("apikey"):
        api_key = current["apikey"]
    elif not api_key:
        print("API key required.")
        return

    secret_key = input(f"Secret API Key [{current.get('secretapikey', '')[:8] + '...' if current.get('secretapikey') else 'not set'}]: ").strip()
    if not secret_key and current.get("secretapikey"):
        secret_key = current["secretapikey"]
    elif not secret_key:
        print("Secret key required.")
        return

    config = {
        "apikey": api_key,
        "secretapikey": secret_key
    }

    # Test before saving
    print("\nTesting credentials...")
    try:
        import requests
        response = requests.post(
            "https://api.porkbun.com/api/json/v3/ping",
            json=config
        )
        result = response.json()
        if result.get("status") == "SUCCESS":
            print(f"Connection successful! Your IP: {result.get('yourIp')}")
            save_config(config)
        else:
            print(f"Error: {result.get('message')}")
            save_anyway = input("Save anyway? [y/N] ").strip().lower()
            if save_anyway == "y":
                save_config(config)
    except ImportError:
        print("Warning: requests not installed, cannot test credentials")
        save_config(config)
    except Exception as e:
        print(f"Error testing: {e}")
        save_anyway = input("Save anyway? [y/N] ").strip().lower()
        if save_anyway == "y":
            save_config(config)

def main():
    parser = argparse.ArgumentParser(
        description="Configure Porkbun API credentials",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python configure.py           Interactive setup
  python configure.py --test    Test current credentials
  python configure.py --show    Show config file location

Environment Variables (alternative to config file):
  PORKBUN_API_KEY       Your API key
  PORKBUN_SECRET_KEY    Your secret API key
        """
    )

    parser.add_argument("--test", "-t", action="store_true", help="Test credentials")
    parser.add_argument("--show", "-s", action="store_true", help="Show config location")

    args = parser.parse_args()

    if args.show:
        print(f"Config file: {CONFIG_FILE}")
        if os.path.exists(CONFIG_FILE):
            print("Status: Configured")
            config = load_config()
            print(f"API Key: {config.get('apikey', '')[:8]}..." if config.get("apikey") else "API Key: Not set")
        else:
            print("Status: Not configured")
        return

    if args.test:
        success = test_credentials()
        sys.exit(0 if success else 1)

    interactive_setup()

if __name__ == "__main__":
    main()
