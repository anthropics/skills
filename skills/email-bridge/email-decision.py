#!/usr/bin/env python3
"""Classify an email: should it continue an existing session or start a new one?"""

import sys
import json
from pathlib import Path

# Keywords that signal "continue the existing conversation"
CONTINUE_KEYWORDS = [
    "继续", "接着", "上次", "刚才", "之前", "上面", "前面",
    "follow up", "continue", "as we discussed", "你刚才",
    "再帮我", "接着做", "继续做", "还是那个", "刚才那个",
    "之前那个", "接着聊", "继续聊",
]

# Keywords that signal "start a fresh session"
NEW_KEYWORDS = [
    "!new", "新对话", "新任务", "新话题", "换个话题",
    "fresh start", "new task", "new topic",
]


def classify(email_body):
    body_lower = email_body.lower()

    # Explicit new session signal
    for kw in NEW_KEYWORDS:
        if kw in body_lower:
            return "new"

    # Explicit continue signal
    for kw in CONTINUE_KEYWORDS:
        if kw in body_lower:
            return "continue"

    # Subject-based: if it's a reply (Re:), likely continuation
    # (handled by caller since subject is separate)

    # Default: start new session for standalone tasks
    return "new"


if __name__ == "__main__":
    if len(sys.argv) < 2:
        # Read from stdin
        body = sys.stdin.read()
    else:
        body = sys.argv[1]

    result = classify(body)
    print(result)
