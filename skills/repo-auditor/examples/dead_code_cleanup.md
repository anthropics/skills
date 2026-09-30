# Example: Dead Code Cleanup

This example demonstrates how to identify and safely remove dead code from a repository.

## Scenario

Your codebase has grown over time and you suspect there's unused code that should be cleaned up.

## Step 1: Run Dead Code Analysis

```bash
$ python scripts/find_dead_code.py /path/to/repo

============================================================
DEAD CODE ANALYSIS REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
SUMMARY
----------------------------------------
  Potentially Unused Functions: 18
  Potentially Unused Classes: 5
  Commented Code Blocks: 12
  Languages Analyzed: python, javascript

----------------------------------------
PYTHON ANALYSIS
----------------------------------------

  Potentially Unused Functions:
    - calculate_old_tax (utils/tax.py:45)
    - send_legacy_email (services/email.py:123)
    - validate_v1_request (api/validators.py:67)
    - format_old_date (utils/dates.py:89)
    - get_deprecated_config (config/legacy.py:34)

  Potentially Unused Classes:
    - OldUserModel (models/user.py:156)
    - LegacyPaymentProcessor (services/payment.py:234)

  Commented Code Blocks:
    - utils/helpers.py:34 (15 lines)
    - services/email.py:78 (8 lines)
    - api/views.py:145 (22 lines)

----------------------------------------
JAVASCRIPT ANALYSIS
----------------------------------------

  Potentially Unused Functions:
    - formatLegacyDate (src/utils/date.js:23)
    - OldButton (src/components/Button.jsx:45)
    - useDeprecatedHook (src/hooks/legacy.js:12)
    - validateOldForm (src/utils/validation.js:78)
    ... and 9 more
```

## Step 2: Verify Each Finding

Before removing any code, verify it's truly unused:

### Check 1: Search for Dynamic Usage

```bash
# Python - Check for getattr/reflection usage
grep -rn "getattr\|__getattribute__\|eval\|exec" --include="*.py" .

# Check if function name is used as a string
grep -rn "calculate_old_tax" --include="*.py" .

# JavaScript - Check for dynamic imports
grep -rn "import\(.*calculate\|require\(.*calculate" --include="*.js" --include="*.jsx" .
```

### Check 2: Check for External Callers

```bash
# Is this an exported API endpoint?
grep -rn "@app.route\|@router\|export" --include="*.py" --include="*.js" . | grep "calculate_old_tax"

# Is it referenced in tests?
grep -rn "calculate_old_tax" tests/ test/
```

### Check 3: Check Git History

```bash
# When was it last modified?
git log -1 --format="%ai %s" -- utils/tax.py

# Who added it and why?
git log --oneline -- utils/tax.py | head -5
git show <commit-hash> --stat
```

### Check 4: Check for TODO/FIXME Comments

```bash
# Is there a reason it's kept?
grep -B5 -A5 "calculate_old_tax" utils/tax.py
```

## Step 3: Categorize Findings

After verification, categorize each finding:

| Function | File | Status | Action |
|----------|------|--------|--------|
| calculate_old_tax | utils/tax.py | Truly unused | Remove |
| send_legacy_email | services/email.py | Used in cron job | Keep |
| validate_v1_request | api/validators.py | API v1 deprecated | Remove after v1 sunset |
| format_old_date | utils/dates.py | Truly unused | Remove |
| OldUserModel | models/user.py | Migration pending | Keep until migration |

## Step 4: Safe Removal Process

### 4.1 Create a Branch

```bash
git checkout -b cleanup/remove-dead-code
```

### 4.2 Remove Verified Dead Code

```python
# Before: utils/tax.py
def calculate_current_tax(amount, rate):
    """Calculate tax using current rules."""
    return amount * rate

def calculate_old_tax(amount):  # REMOVE THIS
    """Deprecated: Old tax calculation."""
    return amount * 0.15

# After: utils/tax.py
def calculate_current_tax(amount, rate):
    """Calculate tax using current rules."""
    return amount * rate
```

### 4.3 Remove Commented Code Blocks

```python
# Before: services/email.py
def send_email(to, subject, body):
    """Send an email."""
    # Old implementation - remove this block
    # smtp = smtplib.SMTP('old-server.com')
    # smtp.login('user', 'pass')
    # msg = MIMEText(body)
    # msg['Subject'] = subject
    # msg['To'] = to
    # smtp.send_message(msg)
    # smtp.quit()
    
    # New implementation
    client = EmailClient()
    client.send(to=to, subject=subject, body=body)

# After: services/email.py
def send_email(to, subject, body):
    """Send an email."""
    client = EmailClient()
    client.send(to=to, subject=subject, body=body)
```

### 4.4 Run Tests

```bash
# Run full test suite
pytest

# Run with coverage to ensure nothing broke
pytest --cov=. --cov-report=html

# Check for import errors
python -c "import myapp"
```

### 4.5 Commit Changes

```bash
git add -A
git commit -m "Remove dead code: calculate_old_tax, format_old_date

- Removed unused calculate_old_tax function (utils/tax.py)
- Removed unused format_old_date function (utils/dates.py)
- Cleaned up 3 commented code blocks
- All tests passing

Verified these functions have no callers via:
- grep search across codebase
- git log analysis
- No dynamic/reflection usage found"
```

## Step 5: Handle Edge Cases

### Edge Case 1: Function Used Only in Tests

```bash
# Check if function is only used in tests
grep -rn "calculate_old_tax" .
# Output:
# utils/tax.py:45:def calculate_old_tax(amount):
# tests/test_tax.py:23:    result = calculate_old_tax(100)
```

**Decision:** Remove both the function AND the test.

### Edge Case 2: Exported but Unused Internally

```javascript
// src/utils/index.js
export { formatDate } from './date';
export { formatLegacyDate } from './date';  // Unused internally but exported
```

**Decision:** Check if external packages depend on this export. If not, remove.

### Edge Case 3: Feature Flag Protected Code

```python
def process_order(order):
    if settings.USE_NEW_PROCESSOR:
        return new_processor(order)
    else:
        return old_processor(order)  # Looks unused but feature flag controlled
```

**Decision:** Keep until feature flag is permanently enabled, then remove.

## Step 6: Verify Cleanup

Re-run the dead code analysis:

```bash
$ python scripts/find_dead_code.py /path/to/repo

============================================================
DEAD CODE ANALYSIS REPORT
============================================================

----------------------------------------
SUMMARY
----------------------------------------
  Potentially Unused Functions: 8  (was 18)
  Potentially Unused Classes: 3    (was 5)
  Commented Code Blocks: 0         (was 12)
  Languages Analyzed: python, javascript
```

## Step 7: Create Pull Request

```bash
git push origin cleanup/remove-dead-code
```

PR Description:
```markdown
## Dead Code Cleanup

This PR removes verified dead code identified during a repository audit.

### Removed
- `calculate_old_tax` (utils/tax.py) - No callers found
- `format_old_date` (utils/dates.py) - No callers found
- `OldButton` component (src/components/Button.jsx) - Replaced by NewButton
- 12 commented code blocks across 5 files

### Verification
Each removal was verified by:
1. Searching for all references in codebase
2. Checking for dynamic/reflection usage
3. Reviewing git history for context
4. Running full test suite

### Not Removed (Pending)
- `validate_v1_request` - Waiting for API v1 sunset (Q2 2024)
- `OldUserModel` - Migration in progress

### Testing
- All unit tests passing
- All integration tests passing
- No import errors
```

## Automation: Prevent Future Dead Code

### Add to CI Pipeline

```yaml
# .github/workflows/code-quality.yml
name: Code Quality

on: [push, pull_request]

jobs:
  dead-code-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install vulture
        run: pip install vulture
        
      - name: Check for dead code
        run: vulture . --min-confidence 90
```

### Add Pre-commit Hook

```yaml
# .pre-commit-config.yaml
repos:
  - repo: https://github.com/jendrikseipp/vulture
    rev: v2.10
    hooks:
      - id: vulture
        args: [--min-confidence, "90"]
```

## Best Practices Summary

1. **Never remove code without verification** - Always search for dynamic usage
2. **Check git history** - Understand why code exists before removing
3. **Remove tests too** - Don't leave orphaned tests for removed code
4. **Document decisions** - Note why certain code was kept
5. **Run full test suite** - Ensure nothing breaks
6. **Review in PR** - Get a second pair of eyes
7. **Automate prevention** - Add dead code checks to CI
