# Language-Specific Vulnerability Patterns

Load the relevant section during Step 1 (Scope Resolution) after identifying languages.

---

## JavaScript / TypeScript (Node.js, React, Next.js, Express)

### Critical imports to flag
```js
eval()                    // arbitrary code execution
Function('return ...')   // same as eval
child_process.exec()     // command injection if user input reaches it
fs.readFile/writeFile    // path traversal if user controls path
```

### Express.js specific
```js
// Missing helmet (security headers)
const app = express()
// Should have: app.use(helmet())

// Body size limits missing (DoS)
app.use(express.json())
// Should have: app.use(express.json({ limit: '10kb' }))

// CORS misconfiguration
app.use(cors({ origin: '*' }))  // too permissive
app.use(cors({ origin: req.headers.origin }))  // reflects any origin

// Trust proxy without validation
app.set('trust proxy', true)  // only safe behind known proxy
```

### React specific
```jsx
<div dangerouslySetInnerHTML={{ __html: userContent }} />  // XSS
<a href={userUrl}>link</a>  // javascript: URL injection
```

### Next.js specific
```js
// Server Actions without auth
export async function deleteUser(id) {   // missing: auth check
  await db.users.delete(id)
}

// API Routes missing method validation
export default function handler(req, res) {
  // Should check: if (req.method !== 'POST') return res.status(405)
  doSensitiveAction()
}
```

---

## Python (Django, Flask, FastAPI)

### Django specific
```python
# Raw SQL
User.objects.raw(f"SELECT * FROM users WHERE name = '{name}'")  # SQLi

# Missing CSRF
@csrf_exempt  # Only OK for APIs with token auth

# Debug mode in production
DEBUG = True  # in settings.py — exposes stack traces

# SECRET_KEY
SECRET_KEY = 'django-insecure-...'  # must be changed for production

# ALLOWED_HOSTS
ALLOWED_HOSTS = ['*']  # too permissive
```

### Flask specific
```python
# Debug mode
app.run(debug=True)  # never in production

# Secret key
app.secret_key = 'dev'  # weak

# eval/exec with user input
eval(request.args.get('expr'))

# render_template_string with user input (SSTI)
render_template_string(f"Hello {name}")  # Server-Side Template Injection
```

### FastAPI specific
```python
# Missing auth dependency
@app.delete("/users/{user_id}")  # No Depends(get_current_user)
async def delete_user(user_id: int):
    ...

# Arbitrary file read
@app.get("/files/{filename}")
async def read_file(filename: str):
    return FileResponse(f"uploads/{filename}")  # path traversal
```

---

## Java (Spring Boot)

### Spring Boot specific
```java
// SQL Injection
String query = "SELECT * FROM users WHERE name = '" + name + "'";
jdbcTemplate.query(query, ...);

// XXE
DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
// Missing: dbf.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true)

// Deserialization
ObjectInputStream ois = new ObjectInputStream(inputStream);
Object obj = ois.readObject();  // only safe with allowlist

// Spring Security — permitAll on sensitive endpoint
.antMatchers("/admin/**").permitAll()

// Actuator endpoints exposed
management.endpoints.web.exposure.include=*  # in application.properties
```

---

## PHP

```php
// Direct user input in queries
$result = mysql_query("SELECT * FROM users WHERE id = " . $_GET['id']);

// File inclusion
include($_GET['page'] . ".php");  // local/remote file inclusion

// eval
eval($_POST['code']);

// extract() with user input
extract($_POST);  // overwrites any variable

// Loose comparison
if ($password == "admin") {}  // use === instead

// Unserialize
unserialize($_COOKIE['data']);  // remote code execution
```

---

## Go

```go
// Command injection
exec.Command("sh", "-c", userInput)

// SQL injection
db.Query("SELECT * FROM users WHERE name = '" + name + "'")

// Path traversal
filePath := filepath.Join("/uploads/", userInput)  // sanitize userInput first

// Insecure TLS
http.Transport{TLSClientConfig: &tls.Config{InsecureSkipVerify: true}}

// Goroutine leak / missing context cancellation
go func() {
  // No done channel or context
  for { ... }
}()
```

---

## Ruby on Rails

```ruby
# SQL injection (safe alternatives use placeholders)
User.where("name = '#{params[:name]}'")  # VULNERABLE
User.where("name = ?", params[:name])   # SAFE

# Mass assignment without strong params
@user.update(params[:user])  # should be params.require(:user).permit(...)

# eval / send with user input
eval(params[:code])
send(params[:method])  # arbitrary method call

# Redirect to user-supplied URL (open redirect)
redirect_to params[:url]

# YAML.load (allows arbitrary object creation)
YAML.load(user_input)  # use YAML.safe_load instead
```

---

## Rust

```rust
// Unsafe blocks — flag for manual review
unsafe {
    // Reason for unsafety should be documented
}

// Integer overflow (debug builds panic, release silently wraps)
let result = a + b;  // use checked_add/saturating_add for financial math

// Unwrap/expect in production code (panics on None/Err)
let value = option.unwrap();  // prefer ? or match

// Deserializing arbitrary types
serde_json::from_str::<serde_json::Value>(&user_input)  // generally safe
// But: bincode::deserialize from untrusted input — can be exploited
```
