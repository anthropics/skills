#!/usr/bin/env python3
"""Email Bridge for Claude Code — send via SMTP, receive via POP3.

Setup:
  1. Copy email-config.example.json to email-config.json
  2. Fill in your sender email, SMTP auth code, and receiver email
  3. Place this script and SKILL.md in your Claude Code project

Usage:
  python3 email-bridge.py send "<subject>" "<body>"
  python3 email-bridge.py check [limit]
"""

import sys
import json
import os
import poplib
import email
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
CONFIG_PATH = SCRIPT_DIR / "email-config.json"
SEEN_PATH = SCRIPT_DIR / ".email-seen.json"


def load_config():
    if not CONFIG_PATH.exists():
        print(f"ERROR: Config not found at {CONFIG_PATH}")
        print("Copy email-config.example.json to email-config.json and fill in your credentials.")
        sys.exit(1)
    return json.loads(CONFIG_PATH.read_text())


def load_seen():
    if SEEN_PATH.exists():
        return set(json.loads(SEEN_PATH.read_text()))
    return set()


def save_seen(seen):
    SEEN_PATH.write_text(json.dumps(list(seen)))


def send(subject, body):
    cfg = load_config()
    msg = MIMEMultipart()
    msg['From'] = cfg['sender']
    msg['To'] = cfg['receiver']
    msg['Subject'] = subject
    msg.attach(MIMEText(body, 'plain', 'utf-8'))

    try:
        smtp_server = cfg.get('smtp_server', 'smtp.163.com')
        smtp_port = cfg.get('smtp_port', 465)
        server = smtplib.SMTP_SSL(smtp_server, smtp_port)
        server.login(cfg['sender'], cfg['smtp_auth'])
        server.sendmail(cfg['sender'], cfg['receiver'], msg.as_string())
        server.quit()
        print("OK: email sent")
    except Exception as e:
        print(f"FAIL: {e}")
        sys.exit(1)


def check(limit=5):
    cfg = load_config()
    seen = load_seen()
    try:
        pop_server = cfg.get('pop_server', 'pop.163.com')
        pop_port = cfg.get('pop_port', 995)
        pop = poplib.POP3_SSL(pop_server, pop_port)
        pop.user(cfg['sender'])
        pop.pass_(cfg['smtp_auth'])  # 163 uses same auth code for SMTP and POP3
        total, _ = pop.stat()
        resp, uid_list, _ = pop.uidl()
        if not uid_list:
            print("No emails")
            pop.quit()
            return

        new = []
        for line in uid_list:
            uid = line.decode().split()[1]
            if uid not in seen:
                new.append(uid)

        if not new:
            print("No new emails")
        else:
            print(f"New: {len(new)} (total: {total})")
            for uid in new[-limit:]:
                idx = None
                for line in uid_list:
                    parts = line.decode().split()
                    if parts[1] == uid:
                        idx = int(parts[0])
                        break
                if idx is None:
                    continue
                resp, lines, _ = pop.retr(idx)
                raw = email.message_from_bytes(b'\n'.join(lines))
                print("---EMAIL---")
                print(f"UID: {uid}")
                print(f"From: {raw['From']}")
                print(f"Subject: {raw['Subject']}")
                print(f"Date: {raw['Date']}")
                body = ""
                if raw.is_multipart():
                    for part in raw.walk():
                        ctype = part.get_content_type()
                        if ctype == 'text/plain':
                            body += part.get_payload(decode=True).decode('utf-8', errors='replace')
                else:
                    body = raw.get_payload(decode=True).decode('utf-8', errors='replace')
                print(f"Body: {body.strip()}")
                print("---END---")
                seen.add(uid)

        pop.quit()
        save_seen(seen)
    except Exception as e:
        print(f"FAIL: {e}")
        sys.exit(1)


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print("Usage: email-bridge.py send <subject> <body>")
        print("       email-bridge.py check [limit]")
        sys.exit(1)

    cmd = sys.argv[1]
    if cmd == 'send':
        if len(sys.argv) < 4:
            print("Usage: email-bridge.py send <subject> <body>")
            sys.exit(1)
        send(sys.argv[2], sys.argv[3])
    elif cmd == 'check':
        limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5
        check(limit)
    else:
        print(f"Unknown command: {cmd}")
        sys.exit(1)
