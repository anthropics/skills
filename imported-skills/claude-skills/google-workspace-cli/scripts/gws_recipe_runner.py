#!/usr/bin/env python3
"""
Google Workspace CLI Recipe Runner — Catalog, search, and execute gws command templates.

Browse 43 recipe command templates (a LOCAL catalog shipped with this skill —
NOT built into the gws CLI), filter by persona, search by keyword, and run
with dry-run support.

IMPORTANT: The gws CLI (github.com/googleworkspace/cli) generates its command
surface dynamically from Google's Discovery Service. Command strings in this
catalog are templates — verify each against `gws --help`, `gws <service> --help`,
or `gws schema <service>.<resource>.<method>` before relying on it.

Usage:
    python3 gws_recipe_runner.py --list
    python3 gws_recipe_runner.py --search "email"
    python3 gws_recipe_runner.py --describe standup-report
    python3 gws_recipe_runner.py --run standup-report --dry-run
    python3 gws_recipe_runner.py --persona pm --list
    python3 gws_recipe_runner.py --list --json
"""

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional


TEMPLATE_NOTE = ("NOTE: Recipe commands are templates from this local catalog (not shipped by "
                 "the gws CLI). Verify each against 'gws --help' / 'gws schema' before use.")


@dataclass
class Recipe:
    name: str
    description: str
    category: str
    services: List[str]
    commands: List[str]
    prerequisites: str = ""


RECIPES: Dict[str, Recipe] = {
    # Email (8)
    "send-email": Recipe("send-email", "Send an email with optional attachments", "email",
                         ["gmail"], ["gws gmail users.messages send me --to {to} --subject {subject} --body {body}"]),
    "reply-to-thread": Recipe("reply-to-thread", "Reply to an existing email thread", "email",
                              ["gmail"], ["gws gmail users.messages reply me --thread-id {thread_id} --body {body}"]),
    "forward-email": Recipe("forward-email", "Forward an email to another recipient", "email",
                            ["gmail"], ["gws gmail users.messages forward me --message-id {msg_id} --to {to}"]),
    "search-emails": Recipe("search-emails", "Search emails with Gmail query syntax", "email",
                            ["gmail"], ["gws gmail users.messages list me --query {query} --json"]),
    "archive-old": Recipe("archive-old", "Archive read emails older than N days", "email",
                          ["gmail"], [
                              "gws gmail users.messages list me --query 'is:read older_than:{days}d' --json",
                              "# Pipe IDs to batch modify to remove INBOX label",
                          ]),
    "label-manager": Recipe("label-manager", "Create, list, and organize Gmail labels", "email",
                            ["gmail"], ["gws gmail users.labels list me --json", "gws gmail users.labels create me --name {name}"]),
    "filter-setup": Recipe("filter-setup", "Create email filters for auto-labeling", "email",
                           ["gmail"], ["gws gmail users.settings.filters create me --criteria {criteria} --action {action}"]),
    "unread-digest": Recipe("unread-digest", "Get digest of unread emails", "email",
                            ["gmail"], ["gws gmail users.messages list me --query 'is:unread' --limit 20 --json"]),

    # Files (7)
    "upload-file": Recipe("upload-file", "Upload a file to Google Drive", "files",
                          ["drive"], ["gws drive files create --name {name} --upload {path} --parents {folder_id}"]),
    "create-sheet": Recipe("create-sheet", "Create a new Google Spreadsheet", "files",
                           ["sheets"], ["gws sheets spreadsheets create --title {title} --json"]),
    "share-file": Recipe("share-file", "Share a Drive file with a user or domain", "files",
                          ["drive"], ["gws drive permissions create {file_id} --type user --role writer --emailAddress {email}"]),
    "export-file": Recipe("export-file", "Export a Google Doc/Sheet as PDF", "files",
                          ["drive"], ["gws drive files export {file_id} --mime application/pdf --output {output}"]),
    "list-files": Recipe("list-files", "List files in a Drive folder", "files",
                         ["drive"], ["gws drive files list --parents {folder_id} --json"]),
    "find-large-files": Recipe("find-large-files", "Find largest files in Drive", "files",
                               ["drive"], ["gws drive files list --orderBy 'quotaBytesUsed desc' --limit 20 --json"]),
    "cleanup-trash": Recipe("cleanup-trash", "Empty Drive trash", "files",
                            ["drive"], ["gws drive files emptyTrash"]),

    # Calendar (6)
    "create-event": Recipe("create-event", "Create a calendar event with attendees", "calendar",
                           ["calendar"], [
                               "gws calendar events insert primary --summary {title} "
                               "--start {start} --end {end} --attendees {attendees}"
                           ]),
    "quick-event": Recipe("quick-event", "Create an event via the calendar helper", "calendar",
                          ["calendar"], ["gws calendar +insert {details}  # see: gws calendar +insert --help"]),
    "find-time": Recipe("find-time", "Find available time slots via free/busy", "calendar",
                        ["calendar"], ["gws calendar freebusy query --json '<freebusy-request>'  # verify: gws schema calendar.freebusy.query"]),
    "today-schedule": Recipe("today-schedule", "Show today's calendar events", "calendar",
                             ["calendar"], ["gws calendar events list primary --timeMin {today_start} --timeMax {today_end} --json"]),
    "meeting-prep": Recipe("meeting-prep", "Prepare for an upcoming meeting (agenda + attendees)", "calendar",
                           ["calendar"], ["gws workflow +meeting-prep"]),
    "reschedule": Recipe("reschedule", "Move an event to a new time", "calendar",
                         ["calendar"], ["gws calendar events patch primary {event_id} --start {new_start} --end {new_end}"]),

    # Reporting (5)
    "standup-report": Recipe("standup-report", "Generate daily standup from calendar and tasks", "reporting",
                             ["calendar", "tasks"], ["gws workflow +standup-report"]),
    "weekly-summary": Recipe("weekly-summary", "Summarize week's emails, events, and tasks", "reporting",
                             ["gmail", "calendar", "tasks"], ["gws workflow +weekly-digest"]),
    "drive-activity": Recipe("drive-activity", "Report on Drive file activity", "reporting",
                             ["drive"], ["gws drive activities list --json"]),
    "email-stats": Recipe("email-stats", "Email volume statistics", "reporting",
                          ["gmail"], [
                              "gws gmail users.messages list me --query 'newer_than:7d' --json",
                              "# Pipe through output_analyzer.py --count",
                          ]),
    "task-progress": Recipe("task-progress", "Report on task completion", "reporting",
                            ["tasks"], ["gws tasks tasks list {tasklist_id} --json"]),

    # Collaboration (5)
    "share-folder": Recipe("share-folder", "Share a Drive folder with a team", "collaboration",
                           ["drive"], ["gws drive permissions create {folder_id} --type group --role writer --emailAddress {group}"]),
    "create-doc": Recipe("create-doc", "Create a Google Doc with initial content", "collaboration",
                         ["docs"], ["gws docs documents create --title {title} --json"]),
    "chat-message": Recipe("chat-message", "Send a message to a Google Chat space", "collaboration",
                           ["chat"], ["gws chat spaces.messages create {space} --text {message}"]),
    "list-spaces": Recipe("list-spaces", "List Google Chat spaces", "collaboration",
                          ["chat"], ["gws chat spaces list --json"]),
    "task-create": Recipe("task-create", "Create a task in Google Tasks", "collaboration",
                          ["tasks"], ["gws tasks tasks insert {tasklist_id} --title {title} --due {due_date}"]),

    # Data (4)
    "sheet-read": Recipe("sheet-read", "Read data from a spreadsheet range", "data",
                         ["sheets"], ["gws sheets spreadsheets.values get {sheet_id} --range {range} --json"]),
    "sheet-write": Recipe("sheet-write", "Write data to a spreadsheet", "data",
                          ["sheets"], ["gws sheets spreadsheets.values update {sheet_id} --range {range} --values {data}"]),
    "sheet-append": Recipe("sheet-append", "Append rows to a spreadsheet", "data",
                           ["sheets"], ["gws sheets spreadsheets.values append {sheet_id} --range {range} --values {data}"]),
    "export-contacts": Recipe("export-contacts", "Export contacts list", "data",
                              ["people"], ["gws people people.connections list me --personFields names,emailAddresses --json"]),

    # Admin (4)
    "list-users": Recipe("list-users", "List all users in the Workspace domain", "admin",
                         ["admin"], ["gws admin users list --domain {domain} --json"],
                         "Requires Admin SDK API and admin.directory.user.readonly scope"),
    "list-groups": Recipe("list-groups", "List all groups in the domain", "admin",
                          ["admin"], ["gws admin groups list --domain {domain} --json"]),
    "user-info": Recipe("user-info", "Get detailed user information", "admin",
                        ["admin"], ["gws admin users get {email} --json"]),
    "audit-logins": Recipe("audit-logins", "Audit recent login activity", "admin",
                           ["admin"], ["gws admin activities list login --json"]),

    # Cross-Service (4)
    "morning-briefing": Recipe("morning-briefing", "Today's events + unread emails + pending tasks", "cross-service",
                               ["gmail", "calendar", "tasks"], [
                                   "gws calendar events list primary --timeMin {today} --maxResults 10 --json",
                                   "gws gmail users.messages list me --query 'is:unread' --limit 10 --json",
                                   "gws tasks tasks list {default_tasklist} --json",
                               ]),
    "eod-wrap": Recipe("eod-wrap", "End-of-day wrap up: summarize completed, pending, tomorrow", "cross-service",
                       ["calendar", "tasks"], [
                           "gws calendar events list primary --timeMin {today_start} --timeMax {today_end} --json",
                           "gws tasks tasks list {default_tasklist} --json",
                       ]),
    "project-status": Recipe("project-status", "Aggregate project status from Drive, Sheets, Tasks", "cross-service",
                             ["drive", "sheets", "tasks"], [
                                 "gws drive files list --query 'name contains {project}' --json",
                                 "gws tasks tasks list {tasklist_id} --json",
                             ]),
    "inbox-zero": Recipe("inbox-zero", "Process inbox to zero: label, archive, reply, task", "cross-service",
                         ["gmail", "tasks"], [
                             "gws gmail users.messages list me --query 'is:inbox' --json",
                             "# Process each: label, archive, or create task",
                         ]),
}

PERSONAS: Dict[str, Dict] = {
    "executive-assistant": {
        "description": "Executive assistant managing schedules, emails, and communications",
        "recipes": ["morning-briefing", "today-schedule", "find-time", "send-email", "reply-to-thread",
                     "standup-report", "meeting-prep", "eod-wrap", "quick-event", "inbox-zero"],
    },
    "pm": {
        "description": "Project manager tracking tasks, meetings, and deliverables",
        "recipes": ["standup-report", "create-event", "find-time", "task-create", "task-progress",
                     "project-status", "weekly-summary", "share-folder", "sheet-read", "morning-briefing"],
    },
    "hr": {
        "description": "HR managing people, onboarding, and communications",
        "recipes": ["list-users", "user-info", "send-email", "create-event", "create-doc",
                     "share-folder", "chat-message", "list-groups", "export-contacts", "today-schedule"],
    },
    "sales": {
        "description": "Sales rep managing client communications and proposals",
        "recipes": ["send-email", "search-emails", "create-event", "find-time", "create-doc",
                     "share-file", "sheet-read", "sheet-write", "export-file", "morning-briefing"],
    },
    "it-admin": {
        "description": "IT administrator managing Workspace configuration and security",
        "recipes": ["list-users", "list-groups", "user-info", "audit-logins", "drive-activity",
                     "find-large-files", "cleanup-trash", "label-manager", "filter-setup", "share-folder"],
    },
    "developer": {
        "description": "Developer using Workspace APIs for automation",
        "recipes": ["sheet-read", "sheet-write", "sheet-append", "upload-file", "create-doc",
                     "chat-message", "task-create", "list-files", "export-file", "send-email"],
    },
    "marketing": {
        "description": "Marketing team member managing campaigns and content",
        "recipes": ["send-email", "create-doc", "share-file", "upload-file", "create-sheet",
                     "sheet-write", "chat-message", "create-event", "email-stats", "weekly-summary"],
    },
    "finance": {
        "description": "Finance team managing spreadsheets and reports",
        "recipes": ["sheet-read", "sheet-write", "sheet-append", "create-sheet", "export-file",
                     "share-file", "send-email", "find-large-files", "drive-activity", "weekly-summary"],
    },
    "legal": {
        "description": "Legal team managing documents and compliance",
        "recipes": ["create-doc", "share-file", "export-file", "search-emails", "send-email",
                     "upload-file", "list-files", "drive-activity", "audit-logins", "find-large-files"],
    },
    "support": {
        "description": "Customer support managing tickets and communications",
        "recipes": ["search-emails", "send-email", "reply-to-thread", "label-manager", "filter-setup",
                     "task-create", "chat-message", "unread-digest", "inbox-zero", "morning-briefing"],
    },
}


def list_recipes(persona: Optional[str], output_json: bool):
    """List all recipes, optionally filtered by persona."""
    if persona:
        if persona not in PERSONAS:
            print(f"Unknown persona: {persona}. Available: {', '.join(PERSONAS.keys())}")
            sys.exit(1)
        recipe_names = PERSONAS[persona]["recipes"]
        recipes = {k: v for k, v in RECIPES.items() if k in recipe_names}
        title = f"Recipes for {persona.upper()}: {PERSONAS[persona]['description']}"
    else:
        recipes = RECIPES
        title = "All 43 Google Workspace CLI Recipes"

    if output_json:
        output = []
        for name, r in recipes.items():
            output.append(asdict(r))
        print(json.dumps(output, indent=2))
        return

    print(f"\n{'='*60}")
    print(f"  {title}")
    print(f"{'='*60}\n")

    by_category: Dict[str, list] = {}
    for name, r in recipes.items():
        by_category.setdefault(r.category, []).append(r)

    for cat, cat_recipes in sorted(by_category.items()):
        print(f"  {cat.upper()} ({len(cat_recipes)})")
        for r in cat_recipes:
            svcs = ",".join(r.services)
            print(f"    {r.name:<24} {r.description:<40} [{svcs}]")
        print()

    print(f"  Total: {len(recipes)} recipes")
    print(f"\n{'='*60}\n")


def search_recipes(keyword: str, output_json: bool):
    """Search recipes by keyword."""
    keyword_lower = keyword.lower()
    matches = {k: v for k, v in RECIPES.items()
               if keyword_lower in k.lower()
               or keyword_lower in v.description.lower()
               or keyword_lower in v.category.lower()
               or any(keyword_lower in s for s in v.services)}

    if output_json:
        print(json.dumps([asdict(r) for r in matches.values()], indent=2))
        return

    print(f"\n  Search results for '{keyword}': {len(matches)} matches\n")
    for name, r in matches.items():
        print(f"    {r.name:<24} {r.description}")
    print()


def describe_recipe(name: str, output_json: bool):
    """Show full details for a recipe."""
    recipe = RECIPES.get(name)
    if not recipe:
        print(f"Unknown recipe: {name}")
        print(f"Use --list to see available recipes")
        sys.exit(1)

    if output_json:
        print(json.dumps(asdict(recipe), indent=2))
        return

    print(f"\n{'='*60}")
    print(f"  Recipe: {recipe.name}")
    print(f"{'='*60}\n")
    print(f"  Description: {recipe.description}")
    print(f"  Category:    {recipe.category}")
    print(f"  Services:    {', '.join(recipe.services)}")
    if recipe.prerequisites:
        print(f"  Prerequisites: {recipe.prerequisites}")
    print(f"\n  Commands:")
    for i, cmd in enumerate(recipe.commands, 1):
        print(f"    {i}. {cmd}")
    print(f"\n  {TEMPLATE_NOTE}")
    print(f"\n{'='*60}\n")


def run_recipe(name: str, dry_run: bool):
    """Execute a recipe (or print commands in dry-run mode)."""
    recipe = RECIPES.get(name)
    if not recipe:
        print(f"Unknown recipe: {name}")
        sys.exit(1)

    if dry_run:
        print(f"\n  [DRY RUN] Recipe: {recipe.name}\n")
        for i, cmd in enumerate(recipe.commands, 1):
            print(f"  {i}. {cmd}")
        print(f"\n  {TEMPLATE_NOTE}")
        print(f"\n  (No commands executed)")
        return

    print(f"\n  Executing recipe: {recipe.name}")
    print(f"  {TEMPLATE_NOTE}\n")
    for cmd in recipe.commands:
        if cmd.startswith("#"):
            print(f"  {cmd}")
            continue
        print(f"  $ {cmd}")
        try:
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=30)
            if result.stdout:
                print(result.stdout)
            if result.returncode != 0 and result.stderr:
                print(f"  Error: {result.stderr.strip()[:200]}")
        except subprocess.TimeoutExpired:
            print(f"  Timeout after 30s")
        except OSError as e:
            print(f"  Execution error: {e}")


def list_personas(output_json: bool):
    """List all available personas."""
    if output_json:
        print(json.dumps(PERSONAS, indent=2))
        return

    print(f"\n{'='*60}")
    print(f"  10 PERSONA BUNDLES")
    print(f"{'='*60}\n")
    for name, p in PERSONAS.items():
        print(f"  {name:<24} {p['description']}")
        print(f"  {'':24} Recipes: {', '.join(p['recipes'][:5])}...")
        print()
    print(f"{'='*60}\n")


def main():
    parser = argparse.ArgumentParser(
        description="Catalog, search, and execute Google Workspace CLI recipes",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --list                           # List all 43 recipes
  %(prog)s --list --persona pm              # Recipes for project managers
  %(prog)s --search "email"                 # Search by keyword
  %(prog)s --describe standup-report        # Full recipe details
  %(prog)s --run standup-report --dry-run   # Preview recipe commands
  %(prog)s --personas                       # List all 10 personas
  %(prog)s --list --json                    # JSON output
        """,
    )
    parser.add_argument("--list", action="store_true", help="List all recipes")
    parser.add_argument("--search", help="Search recipes by keyword")
    parser.add_argument("--describe", help="Show full details for a recipe")
    parser.add_argument("--run", help="Execute a recipe")
    parser.add_argument("--dry-run", action="store_true", help="Print commands without executing")
    parser.add_argument("--persona", help="Filter recipes by persona")
    parser.add_argument("--personas", action="store_true", help="List all personas")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    args = parser.parse_args()

    if not any([args.list, args.search, args.describe, args.run, args.personas]):
        parser.print_help()
        return

    if args.personas:
        list_personas(args.json)
        return

    if args.list:
        list_recipes(args.persona, args.json)
        return

    if args.search:
        search_recipes(args.search, args.json)
        return

    if args.describe:
        describe_recipe(args.describe, args.json)
        return

    if args.run:
        run_recipe(args.run, args.dry_run)
        return


if __name__ == "__main__":
    main()
