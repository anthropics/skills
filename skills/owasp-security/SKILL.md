---
name: owasp-security
description: Use when reviewing code for security vulnerabilities, implementing authentication/authorization, handling user input, or discussing web application security. Covers OWASP Top 10:2025, ASVS 5.0, and Agentic AI security (2026).
---

# OWASP Security Best Practices Skill

Apply these security standards when writing or reviewing code.

## Quick Reference: OWASP Top 10:2025

| # | Vulnerability | Key Prevention |
|---|---------------|----------------|
| A01 | Broken Access Control | Deny by default, enforce server-side, verify ownership |
| A02 | Security Misconfiguration | Harden configs, disable defaults, minimize features |
| A03 | Supply Chain Failures | Lock versions, verify integrity, audit dependencies |
| A04 | Cryptographic Failures | TLS 1.2+, AES-256-GCM, Argon2/bcrypt for passwords |
| A05 | Injection | Parameterized queries, input validation, safe APIs |
| A06 | Insecure Design | Threat model, rate limit, design security controls |
| A07 | Auth Failures | MFA, check breached passwords, secure sessions |
| A08 | Integrity Failures | Sign packages, SRI for CDN, safe serialization |
| A09 | Logging Failures | Log security events, structured format, alerting |
| A10 | Exception Handling | Fail-closed, hide internals, log with context |

## Security Code Review Checklist

When reviewing code, check for these issues:

### Input Handling
- [ ] All user input validated server-side
- [ ] Using parameterized queries (not string concatenation)
- [ ] Input length limits enforced
- [ ] Allowlist validation preferred over denylist

### Authentication & Sessions
- [ ] Passwords hashed with Argon2/bcrypt (not MD5/SHA1)
- [ ] Session tokens have sufficient entropy (128+ bits)
- [ ] Sessions invalidated on logout
- [ ] MFA available for sensitive operations

### Access Control
- [ ] Authorization checked on every request
- [ ] Using object references user cannot manipulate
- [ ] Deny by default policy
- [ ] Privilege escalation paths reviewed

### Data Protection
- [ ] Sensitive data encrypted at rest
- [ ] TLS for all data in transit
- [ ] No sensitive data in URLs/logs
- [ ] Secrets in environment/vault (not code)

### Error Handling
- [ ] No stack traces exposed to users
- [ ] Fail-closed on errors (deny, not allow)
- [ ] All exceptions logged with context
- [ ] Consistent error responses (no enumeration)

## Secure Code Patterns

### SQL Injection Prevention
```python
# UNSAFE
cursor.execute(f"SELECT * FROM users WHERE id = {user_id}")

# SAFE
cursor.execute("SELECT * FROM users WHERE id = %s", (user_id,))
```

### Command Injection Prevention
```python
# UNSAFE
os.system(f"convert {filename} output.png")

# SAFE
subprocess.run(["convert", filename, "output.png"], shell=False)
```

### Password Storage
```python
# UNSAFE
hashlib.md5(password.encode()).hexdigest()

# SAFE
from argon2 import PasswordHasher
PasswordHasher().hash(password)
```

### Access Control
```python
# UNSAFE - No authorization check
@app.route('/api/user/<user_id>')
def get_user(user_id):
    return db.get_user(user_id)

# SAFE - Authorization enforced
@app.route('/api/user/<user_id>')
@login_required
def get_user(user_id):
    if current_user.id != user_id and not current_user.is_admin:
        abort(403)
    return db.get_user(user_id)
```

### Error Handling
```python
# UNSAFE - Exposes internals
@app.errorhandler(Exception)
def handle_error(e):
    return str(e), 500

# SAFE - Fail-closed, log context
@app.errorhandler(Exception)
def handle_error(e):
    error_id = uuid.uuid4()
    logger.exception(f"Error {error_id}: {e}")
    return {"error": "An error occurred", "id": str(error_id)}, 500
```

### Fail-Closed Pattern
```python
# UNSAFE - Fail-open
def check_permission(user, resource):
    try:
        return auth_service.check(user, resource)
    except Exception:
        return True  # DANGEROUS!

# SAFE - Fail-closed
def check_permission(user, resource):
    try:
        return auth_service.check(user, resource)
    except Exception as e:
        logger.error(f"Auth check failed: {e}")
        return False  # Deny on error
```

## Agentic AI Security (OWASP 2026)

When building or reviewing AI agent systems, check for:

| Risk | Description | Mitigation |
|------|-------------|------------|
| ASI01: Goal Hijack | Prompt injection alters agent objectives | Input sanitization, goal boundaries, behavioral monitoring |
| ASI02: Tool Misuse | Tools used in unintended ways | Least privilege, fine-grained permissions, validate I/O |
| ASI03: Privilege Abuse | Credential escalation across agents | Short-lived scoped tokens, identity verification |
| ASI04: Supply Chain | Compromised plugins/MCP servers | Verify signatures, sandbox, allowlist plugins |
| ASI05: Code Execution | Unsafe code generation/execution | Sandbox execution, static analysis, human approval |
| ASI06: Memory Poisoning | Corrupted RAG/context data | Validate stored content, segment by trust level |
| ASI07: Agent Comms | Spoofing between agents | Authenticate, encrypt, verify message integrity |
| ASI08: Cascading Failures | Errors propagate across systems | Circuit breakers, graceful degradation, isolation |
| ASI09: Trust Exploitation | Social engineering via AI | Label AI content, user education, verification steps |
| ASI10: Rogue Agents | Compromised agents acting maliciously | Behavior monitoring, kill switches, anomaly detection |

### Agent Security Checklist

- [ ] All agent inputs sanitized and validated
- [ ] Tools operate with minimum required permissions
- [ ] Credentials are short-lived and scoped
- [ ] Third-party plugins verified and sandboxed
- [ ] Code execution happens in isolated environments
- [ ] Agent communications authenticated and encrypted
- [ ] Circuit breakers between agent components
- [ ] Human approval for sensitive operations
- [ ] Behavior monitoring for anomaly detection
- [ ] Kill switch available for agent systems

## ASVS 5.0 Key Requirements

### Level 1 (All Applications)
- Passwords minimum 12 characters
- Check against breached password lists
- Rate limiting on authentication
- Session tokens 128+ bits entropy
- HTTPS everywhere

### Level 2 (Sensitive Data)
- All L1 requirements plus:
- MFA for sensitive operations
- Cryptographic key management
- Comprehensive security logging
- Input validation on all parameters

### Level 3 (Critical Systems)
- All L1/L2 requirements plus:
- Hardware security modules for keys
- Threat modeling documentation
- Advanced monitoring and alerting
- Penetration testing validation

## Language-Specific Security Quirks

> **Important:** The examples below are illustrative starting points, not exhaustive. When reviewing code, think like a senior security researcher: consider the language's memory model, type system, standard library pitfalls, ecosystem-specific attack vectors, and historical CVE patterns. Each language has deeper quirks beyond what's listed here.

Different languages have unique security pitfalls. Here are the top 20 languages with key security considerations. **Go deeper for the specific language you're working in:**

---

### JavaScript / TypeScript
**Main Risks:** Prototype pollution, XSS, eval injection
```javascript
// UNSAFE: Prototype pollution
Object.assign(target, userInput)
// SAFE: Use null prototype or validate keys
Object.assign(Object.create(null), validated)

// UNSAFE: eval injection
eval(userCode)
// SAFE: Never use eval with user input
```
**Watch for:** `eval()`, `innerHTML`, `document.write()`, prototype chain manipulation, `__proto__`

---

### Python
**Main Risks:** Pickle deserialization, format string injection, shell injection
```python
# UNSAFE: Pickle RCE
pickle.loads(user_data)
# SAFE: Use JSON or validate source
json.loads(user_data)

# UNSAFE: Format string injection
query = "SELECT * FROM users WHERE name = '%s'" % user_input
# SAFE: Parameterized
cursor.execute("SELECT * FROM users WHERE name = %s", (user_input,))
```
**Watch for:** `pickle`, `eval()`, `exec()`, `os.system()`, `subprocess` with `shell=True`

---

### Java
**Main Risks:** Deserialization RCE, XXE, JNDI injection
```java
// UNSAFE: Arbitrary deserialization
ObjectInputStream ois = new ObjectInputStream(userStream);
Object obj = ois.readObject();

// SAFE: Use allowlist or JSON
ObjectMapper mapper = new ObjectMapper();
mapper.readValue(json, SafeClass.class);
```
**Watch for:** `ObjectInputStream`, `Runtime.exec()`, XML parsers without XXE protection, JNDI lookups

---

### C#
**Main Risks:** Deserialization, SQL injection, path traversal
```csharp
// UNSAFE: BinaryFormatter RCE
BinaryFormatter bf = new BinaryFormatter();
object obj = bf.Deserialize(stream);

// SAFE: Use System.Text.Json
var obj = JsonSerializer.Deserialize<SafeType>(json);
```
**Watch for:** `BinaryFormatter`, `JavaScriptSerializer`, `TypeNameHandling.All`, raw SQL strings

---

### PHP
**Main Risks:** Type juggling, file inclusion, object injection
```php
// UNSAFE: Type juggling in auth
if ($password == $stored_hash) { ... }
// SAFE: Use strict comparison
if (hash_equals($stored_hash, $password)) { ... }

// UNSAFE: File inclusion
include($_GET['page'] . '.php');
// SAFE: Allowlist pages
$allowed = ['home', 'about']; include(in_array($page, $allowed) ? "$page.php" : 'home.php');
```
**Watch for:** `==` vs `===`, `include/require`, `unserialize()`, `preg_replace` with `/e`, `extract()`

---

### Go
**Main Risks:** Race conditions, template injection, slice bounds
```go
// UNSAFE: Race condition
go func() { counter++ }()
// SAFE: Use sync primitives
atomic.AddInt64(&counter, 1)

// UNSAFE: Template injection
template.HTML(userInput)
// SAFE: Let template escape
{{.UserInput}}
```
**Watch for:** Goroutine data races, `template.HTML()`, `unsafe` package, unchecked slice access

---

### Ruby
**Main Risks:** Mass assignment, YAML deserialization, regex DoS
```ruby
# UNSAFE: Mass assignment
User.new(params[:user])
# SAFE: Strong parameters
User.new(params.require(:user).permit(:name, :email))

# UNSAFE: YAML RCE
YAML.load(user_input)
# SAFE: Use safe_load
YAML.safe_load(user_input)
```
**Watch for:** YAML.load, Marshal.load, eval, send with user input, .permit!

---

### Rust
**Main Risks:** Unsafe blocks, FFI boundary issues, integer overflow in release
```rust
// CAUTION: Unsafe bypasses safety
unsafe { ptr::read(user_ptr) }

// CAUTION: Release integer overflow
let x: u8 = 255;
let y = x + 1; // Wraps to 0 in release!
// SAFE: Use checked arithmetic
let y = x.checked_add(1).unwrap_or(255);
```
**Watch for:** `unsafe` blocks, FFI calls, integer overflow in release builds, `.unwrap()` on untrusted input

---

### Swift
**Main Risks:** Force unwrapping crashes, Objective-C interop
```swift
// UNSAFE: Force unwrap on untrusted data
let value = jsonDict["key"]!
// SAFE: Safe unwrapping
guard let value = jsonDict["key"] else { return }

// UNSAFE: Format string
String(format: userInput, args)
// SAFE: Don't use user input as format
```
**Watch for:** force unwrap (!), try!, ObjC bridging, NSSecureCoding misuse

---

### Kotlin
**Main Risks:** Null safety bypass, Java interop, serialization
```kotlin
// UNSAFE: Platform type from Java
val len = javaString.length // NPE if null
// SAFE: Explicit null check
val len = javaString?.length ?: 0

// UNSAFE: Reflection
clazz.getDeclaredMethod(userInput)
// SAFE: Allowlist methods
```
**Watch for:** Java interop nulls (! operator), reflection, serialization, platform types

---

### C / C++
**Main Risks:** Buffer overflow, use-after-free, format string
```c
// UNSAFE: Buffer overflow
char buf[10]; strcpy(buf, userInput);
// SAFE: Bounds checking
strncpy(buf, userInput, sizeof(buf) - 1);

// UNSAFE: Format string
printf(userInput);
// SAFE: Always use format specifier
printf("%s", userInput);
```
**Watch for:** `strcpy`, `sprintf`, `gets`, pointer arithmetic, manual memory management, integer overflow

---

### Scala
**Main Risks:** XML external entities, serialization, pattern matching exhaustiveness
```scala
// UNSAFE: XXE
val xml = XML.loadString(userInput)
// SAFE: Disable external entities
val factory = SAXParserFactory.newInstance()
factory.setFeature("http://xml.org/sax/features/external-general-entities", false)
```
**Watch for:** Java interop issues, XML parsing, `Serializable`, exhaustive pattern matching

---

### R
**Main Risks:** Code injection, file path manipulation
```r
# UNSAFE: eval injection
eval(parse(text = user_input))
# SAFE: Never parse user input as code

# UNSAFE: Path traversal
read.csv(paste0("data/", user_file))
# SAFE: Validate filename
if (grepl("^[a-zA-Z0-9]+\\.csv$", user_file)) read.csv(...)
```
**Watch for:** `eval()`, `parse()`, `source()`, `system()`, file path manipulation

---

### Perl
**Main Risks:** Regex injection, open() injection, taint mode bypass
```perl
# UNSAFE: Regex DoS
$input =~ /$user_pattern/;
# SAFE: Use quotemeta
$input =~ /\Q$user_pattern\E/;

# UNSAFE: open() command injection
open(FILE, $user_file);
# SAFE: Three-argument open
open(my $fh, '<', $user_file);
```
**Watch for:** Two-arg `open()`, regex from user input, backticks, `eval`, disabled taint mode

---

### Shell (Bash)
**Main Risks:** Command injection, word splitting, globbing
```bash
# UNSAFE: Unquoted variables
rm $user_file
# SAFE: Always quote
rm "$user_file"

# UNSAFE: eval
eval "$user_command"
# SAFE: Never eval user input
```
**Watch for:** Unquoted variables, `eval`, backticks, `$(...)` with user input, missing `set -euo pipefail`

---

### Lua
**Main Risks:** Sandbox escape, loadstring injection
```lua
-- UNSAFE: Code injection
loadstring(user_code)()
-- SAFE: Use sandboxed environment with restricted functions
```
**Watch for:** `loadstring`, `loadfile`, `dofile`, `os.execute`, `io` library, debug library

---

### Elixir
**Main Risks:** Atom exhaustion, code injection, ETS access
```elixir
# UNSAFE: Atom exhaustion DoS
String.to_atom(user_input)
# SAFE: Use existing atoms only
String.to_existing_atom(user_input)

# UNSAFE: Code injection
Code.eval_string(user_input)
# SAFE: Never eval user input
```
**Watch for:** `String.to_atom`, `Code.eval_string`, `:erlang.binary_to_term`, ETS public tables

---

### Dart / Flutter
**Main Risks:** Platform channel injection, insecure storage
```dart
// UNSAFE: Storing secrets in SharedPreferences
prefs.setString('auth_token', token);
// SAFE: Use flutter_secure_storage
secureStorage.write(key: 'auth_token', value: token);
```
**Watch for:** Platform channel data, `dart:mirrors`, `Function.apply`, insecure local storage

---

### PowerShell
**Main Risks:** Command injection, execution policy bypass
```powershell
# UNSAFE: Injection
Invoke-Expression $userInput
# SAFE: Avoid Invoke-Expression with user data

# UNSAFE: Unvalidated path
Get-Content $userPath
# SAFE: Validate path is within allowed directory
```
**Watch for:** `Invoke-Expression`, `& $userVar`, `Start-Process` with user args, `-ExecutionPolicy Bypass`

---

### SQL (All Dialects)
**Main Risks:** Injection, privilege escalation, data exfiltration
```sql
-- UNSAFE: String concatenation
"SELECT * FROM users WHERE id = " + userId

-- SAFE: Parameterized query (language-specific)
-- Use prepared statements in ALL cases
```
**Watch for:** Dynamic SQL, `EXECUTE IMMEDIATE`, stored procedures with dynamic queries, privilege grants

---

## Deep Security Analysis Mindset

When reviewing any language, think like a senior security researcher:

1. **Memory Model:** How does the language handle memory? Managed vs manual? GC pauses exploitable?
2. **Type System:** Weak typing = type confusion attacks. Look for coercion exploits.
3. **Serialization:** Every language has its pickle/Marshal equivalent. All are dangerous.
4. **Concurrency:** Race conditions, TOCTOU, atomicity failures specific to the threading model.
5. **FFI Boundaries:** Native interop is where type safety breaks down.
6. **Standard Library:** Historic CVEs in std libs (Python urllib, Java XML, Ruby OpenSSL).
7. **Package Ecosystem:** Typosquatting, dependency confusion, malicious packages.
8. **Build System:** Makefile/gradle/npm script injection during builds.
9. **Runtime Behavior:** Debug vs release differences (Rust overflow, C++ assertions).
10. **Error Handling:** How does the language fail? Silently? With stack traces? Fail-open?

**For any language not listed:** Research its specific CWE patterns, CVE history, and known footguns. The examples above are entry points, not complete coverage.

## When to Apply This Skill

Use this skill when:
- Writing authentication or authorization code
- Handling user input or external data
- Implementing cryptography or password storage
- Reviewing code for security vulnerabilities
- Designing API endpoints
- Building AI agent systems
- Configuring application security settings
- Handling errors and exceptions
- Working with third-party dependencies
- **Working in any language** - apply the deep analysis mindset above
