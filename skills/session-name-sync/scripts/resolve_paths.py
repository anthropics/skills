"""Resolve Claude Code project dir and cc-connect session file dynamically."""
import os, hashlib, re, glob, json

def resolve_paths():
    # Find cc_project_dir by locating the current session's JSONL file
    # This works regardless of cwd (e.g. skill working inside .claude/skills/)
    session_id = os.environ.get('CLAUDE_CODE_SESSION_ID', '')
    cc_project_dir = None

    if session_id:
        # Scan ~/.claude/projects/ for the directory containing our session JSONL
        projects_base = os.path.expanduser('~/.claude/projects/')
        if os.path.isdir(projects_base):
            for entry in os.listdir(projects_base):
                candidate = os.path.join(projects_base, entry)
                if os.path.isdir(candidate):
                    jsonl_path = os.path.join(candidate, f'{session_id}.jsonl')
                    if os.path.isfile(jsonl_path):
                        cc_project_dir = candidate
                        break

    # Fallback: use cwd-based slug (original behavior)
    if not cc_project_dir:
        cwd = os.getcwd()
        slug = cwd.replace('/', '-')
        cc_project_dir = os.path.expanduser(f'~/.claude/projects/{slug}/')

    config_path = os.path.expanduser('~/.cc-connect/config.toml')
    cc_sessions_dir = os.path.expanduser('~/.cc-connect/sessions/')
    cc_file = None
    try:
        with open(config_path) as f:
            content = f.read()
        m_name = re.search(r'\[\[projects\]\]\s*\nname\s*=\s*"([^"]+)"', content)
        m_dir = re.search(r'work_dir\s*=\s*"([^"]+)"', content)
        if m_name and m_dir:
            project_name = m_name.group(1)
            work_dir = m_dir.group(1)
            hash8 = hashlib.sha256(work_dir.encode()).hexdigest()[:8]
            cc_file = os.path.join(cc_sessions_dir, f'{project_name}_{hash8}.json')
    except FileNotFoundError:
        pass

    return cc_project_dir, cc_file

if __name__ == '__main__':
    cc_project_dir, cc_file = resolve_paths()
    print(f"cc_project_dir={cc_project_dir}")
    print(f"cc_file={cc_file}")