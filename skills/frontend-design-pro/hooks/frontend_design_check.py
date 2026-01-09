#!/usr/bin/env python3
"""
Frontend Design Quality Hook for Claude Code
Warns about generic AI aesthetics patterns in frontend code.
"""

import json
import os
import sys
import re
from datetime import datetime

DEBUG_LOG_FILE = "/tmp/frontend-design-check-log.txt"

def debug_log(message):
    """Append debug message to log file with timestamp."""
    try:
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
        with open(DEBUG_LOG_FILE, "a") as f:
            f.write(f"[{timestamp}] {message}\n")
    except Exception:
        pass

# File extensions to check
FRONTEND_EXTENSIONS = {'.tsx', '.jsx', '.ts', '.js', '.css', '.scss', '.html', '.vue', '.svelte'}

# Patterns to detect generic AI aesthetics
GENERIC_PATTERNS = [
    {
        "ruleName": "generic_font_inter",
        "patterns": [
            r"font-family[:\s]*['\"]?Inter",
            r"fontFamily[:\s]*['\"]?Inter",
            r"--font[^:]*:[^;]*Inter",
        ],
        "reminder": """⚠️ Frontend Design Warning: Detected use of 'Inter' font.

Inter is the most common "AI slop" font choice. Consider distinctive alternatives:
- **Code aesthetic**: JetBrains Mono, Fira Code, Berkeley Mono
- **Editorial**: Playfair Display, Crimson Pro, Newsreader
- **Technical**: IBM Plex Sans/Mono, Space Mono
- **Distinctive**: Bricolage Grotesque, Syne, Outfit

The frontend-design-pro skill recommends avoiding Inter, Roboto, Arial, and system fonts.""",
    },
    {
        "ruleName": "generic_font_roboto",
        "patterns": [
            r"font-family[:\s]*['\"]?Roboto",
            r"fontFamily[:\s]*['\"]?Roboto",
        ],
        "reminder": """⚠️ Frontend Design Warning: Detected use of 'Roboto' font.

Roboto is a generic font choice. Consider distinctive alternatives:
- **Code aesthetic**: JetBrains Mono, Fira Code
- **Editorial**: Playfair Display, Crimson Pro
- **Technical**: IBM Plex Sans/Mono

The frontend-design-pro skill recommends avoiding generic fonts.""",
    },
    {
        "ruleName": "purple_gradient",
        "patterns": [
            r"gradient[^;]*purple",
            r"gradient[^;]*#[89a-fA-F][0-9a-fA-F][0-9a-fA-F][89a-fA-F][fF][fF]",
            r"linear-gradient[^)]*violet",
            r"from-purple.*to-",
            r"bg-gradient.*purple",
        ],
        "reminder": """⚠️ Frontend Design Warning: Detected purple gradient pattern.

Purple gradients on white backgrounds are the quintessential "AI slop" aesthetic.

Consider alternatives:
- **Warm gradients**: Coral → Amber, Peach → Rose
- **Cool gradients**: Teal → Cyan, Navy → Sky
- **Earth tones**: Forest → Sage, Terracotta → Sand
- **Dramatic**: Deep black → Charcoal with accent color highlights

Or use solid colors with texture/depth instead of gradients.""",
    },
    {
        "ruleName": "generic_system_font",
        "patterns": [
            r"font-family[:\s]*system-ui",
            r"font-family[:\s]*-apple-system",
            r"fontFamily[:\s]*['\"]?system-ui",
        ],
        "reminder": """⚠️ Frontend Design Warning: Detected system font usage.

System fonts are safe but generic. For distinctive interfaces, load a custom font.

Quick wins:
- Google Fonts: https://fonts.google.com
- Add: <link href="https://fonts.googleapis.com/css2?family=YOUR_FONT&display=swap" rel="stylesheet">

Recommended distinctive fonts:
- Bricolage Grotesque, Syne (display)
- IBM Plex Sans, Space Grotesk (body)
- JetBrains Mono, Fira Code (code)""",
    },
]


def get_state_file(session_id):
    """Get session-specific state file path."""
    return os.path.expanduser(f"~/.claude/frontend_design_warnings_{session_id}.json")


def load_state(session_id):
    """Load the state of shown warnings from file."""
    state_file = get_state_file(session_id)
    if os.path.exists(state_file):
        try:
            with open(state_file, "r") as f:
                return set(json.load(f))
        except (json.JSONDecodeError, IOError):
            return set()
    return set()


def save_state(session_id, shown_warnings):
    """Save the state of shown warnings to file."""
    state_file = get_state_file(session_id)
    try:
        os.makedirs(os.path.dirname(state_file), exist_ok=True)
        with open(state_file, "w") as f:
            json.dump(list(shown_warnings), f)
    except IOError:
        pass


def is_frontend_file(file_path):
    """Check if file is a frontend file based on extension."""
    _, ext = os.path.splitext(file_path.lower())
    return ext in FRONTEND_EXTENSIONS


def check_patterns(content):
    """Check if content matches any generic aesthetic patterns."""
    for pattern_config in GENERIC_PATTERNS:
        for pattern in pattern_config["patterns"]:
            if re.search(pattern, content, re.IGNORECASE):
                return pattern_config["ruleName"], pattern_config["reminder"]
    return None, None


def extract_content_from_input(tool_name, tool_input):
    """Extract content to check from tool input."""
    if tool_name == "Write":
        return tool_input.get("content", "")
    elif tool_name == "Edit":
        return tool_input.get("new_string", "")
    return ""


def main():
    """Main hook function."""
    # Check if hook is enabled (default: enabled)
    if os.environ.get("DISABLE_FRONTEND_DESIGN_CHECK", "0") == "1":
        sys.exit(0)

    # Read input from stdin
    try:
        raw_input = sys.stdin.read()
        input_data = json.loads(raw_input)
    except json.JSONDecodeError as e:
        debug_log(f"JSON decode error: {e}")
        sys.exit(0)

    session_id = input_data.get("session_id", "default")
    tool_name = input_data.get("tool_name", "")
    tool_input = input_data.get("tool_input", {})

    if tool_name not in ["Edit", "Write"]:
        sys.exit(0)

    file_path = tool_input.get("file_path", "")
    if not file_path or not is_frontend_file(file_path):
        sys.exit(0)

    content = extract_content_from_input(tool_name, tool_input)
    if not content:
        sys.exit(0)

    rule_name, reminder = check_patterns(content)

    if rule_name and reminder:
        warning_key = f"{file_path}-{rule_name}"
        shown_warnings = load_state(session_id)

        if warning_key not in shown_warnings:
            shown_warnings.add(warning_key)
            save_state(session_id, shown_warnings)

            # Output warning to stderr and block execution
            print(reminder, file=sys.stderr)
            sys.exit(2)  # Block tool execution

    sys.exit(0)


if __name__ == "__main__":
    main()
