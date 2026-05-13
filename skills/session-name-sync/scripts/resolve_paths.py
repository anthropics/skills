"""Resolve Claude Code project dir and cc-connect session file dynamically."""
import os, hashlib, re

def resolve_paths():
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