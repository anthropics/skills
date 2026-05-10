---
name: sodp
description: Integrate SODP (State-Oriented Data Protocol) into a project. Use this skill when the user wants to add real-time state synchronization over WebSocket to their app — replacing polling, REST SSE, or manual socket management. Covers client setup (TypeScript, React, Python, Java), server setup (Rust, Go), watching state keys, writing state, and presence (live cursors, online indicators).
license: Complete terms in LICENSE.txt
---

# SODP Integration Skill

SODP (State-Oriented Data Protocol) is an open protocol for continuous state synchronization over WebSocket. Instead of polling or request/response, clients subscribe to named state keys and receive only the changed fields as deltas on every mutation.

```
client → WATCH "game.score"
server → STATE_INIT { value: null, initialized: false }
client → CALL state.set "game.score" { value: 42 }
server → DELTA { value: 42 }          (sent to ALL watchers)
```

One mutation to a 100-field object sends only the changed fields. Reconnect replays missed deltas automatically.

---

## Step 1 — Understand what the user needs

Ask or infer:
- Are they building a **client** (browser, mobile, backend service consuming state) or a **server** (the SODP server itself)?
- What **language/framework** are they using?
- What **state** do they want to sync? (game scores, collaborative cursors, live dashboards, etc.)

Detect the language from project files: `package.json` (TypeScript/React), `pyproject.toml` / `requirements.txt` (Python), `pom.xml` (Java/Maven), `build.gradle` (Java/Gradle), `go.mod` (Go server embedding).

---

## Step 2 — Client setup

### TypeScript / JavaScript

Install: `npm install @sodp/client`

Create `src/lib/sodp.ts`:
```typescript
import { SodpClient } from "@sodp/client";

export const sodp = new SodpClient(
  process.env.SODP_URL ?? "ws://localhost:7777"
);
```

Watch a key:
```typescript
const unsub = sodp.watch<{ score: number }>("game.score", (value, meta) => {
  if (!meta.initialized) return; // key not yet written
  console.log("score:", value?.score, "v" + meta.version);
  // meta.source: "cache" | "init" | "delta"
});
unsub(); // stop watching
```

Write state:
```typescript
await sodp.set("game.score", { score: 42 });           // replace full value
await sodp.patch("game.player", { health: 80 });        // merge fields only
await sodp.state("game.player").setIn("/position/x", 5); // nested field
await sodp.state("game.player").delete();               // remove key
```

Presence (auto-removed on disconnect):
```typescript
await sodp.presence("collab.cursors", `/user_${userId}`, { name, color });
```

---

### React

Install: `npm install @sodp/client @sodp/react`

Wrap the app in `main.tsx` or `App.tsx`:
```tsx
import { SODPProvider } from "@sodp/react";

<SODPProvider url={import.meta.env.VITE_SODP_URL ?? "ws://localhost:7777"}>
  <App />
</SODPProvider>
```

Use hooks in components:
```tsx
import { useSodpState, useSodpStates, useSodpRef, useSodpConnected } from "@sodp/react";

// Single key — re-renders on every update
const [score, meta] = useSodpState<{ value: number }>("game.score");
if (!meta?.initialized) return <div>Loading...</div>;

// Multiple keys
const states = useSodpStates<number>(["game.score", "game.timer"]);

// Write without subscribing
const ref = useSodpRef("game.player");
<button onClick={() => ref.patch({ health: 0 })}>Kill</button>

// Connection status
const connected = useSodpConnected();
```

---

### Python

Install: `pip install sodp-client`

```python
import asyncio, os
from sodp import SodpClient

client = SodpClient(os.getenv("SODP_URL", "ws://localhost:7777"))

async def main():
    await client.ready

    # Watch
    unsub = client.watch("game.score", lambda value, meta: print(value))

    # Write
    await client.set("game.score", {"value": 42})
    await client.patch("game.player", {"health": 80})
    await client.state("game.player").set_in("/position/x", 5)
    await client.state("game.player").delete()

    # Presence
    await client.presence("collab.cursors", f"/user_{user_id}", {"name": name})

    client.close()

asyncio.run(main())
```

---

### Java

Add to `pom.xml`:
```xml
<dependency>
  <groupId>site.orkestri</groupId>
  <artifactId>sodp-client</artifactId>
  <version>0.2.2</version>
</dependency>
```

Or Gradle: `implementation 'site.orkestri:sodp-client:0.2.2'`

```java
import site.orkestri.sodp.SodpClient;

SodpClient client = SodpClient.builder(
    System.getenv().getOrDefault("SODP_URL", "ws://localhost:7777"))
    .build();

client.ready().get(); // wait for connection

// Watch
Runnable unsub = client.watch("game.score", JsonNode.class, (value, meta) -> {
    if (!meta.initialized()) return;
    System.out.println("score: " + value + " v" + meta.version());
});

// Write
client.set("game.player", new PlayerState("Alice", 100)).get();
client.patch("game.player", Map.of("health", 80)).get();
client.setIn("game.player", "/position/x", 5.0).get();
client.delete("game.player").get();
client.presence("collab.cursors", "/user_alice", Map.of("name", "Alice")).get();

client.close();
```

Spring Boot bean:
```java
@Bean
public SodpClient sodpClient(@Value("${sodp.url:ws://localhost:7777}") String url) {
    return SodpClient.builder(url).build();
}
```

---

## Step 3 — Server setup

### Run with Docker (fastest)

```bash
docker run -p 7777:7777 ghcr.io/orkestri/sodp-server:latest

# With persistence + JWT + ACL
docker run -p 7777:7777 \
  -e SODP_JWT_SECRET=your-secret \
  -e SODP_ACL_FILE=/config/acl.json \
  -v $(pwd)/config:/config \
  -v sodp-data:/data \
  ghcr.io/orkestri/sodp-server:latest 0.0.0.0:7777 /data
```

### Rust server (standalone)

```bash
cargo install --git https://github.com/orkestri/SODP sodp-server
sodp-server 0.0.0.0:7777
sodp-server 0.0.0.0:7777 /var/lib/sodp/log          # with persistence
sodp-server 0.0.0.0:7777 /var/lib/sodp/log schema.json  # with schema validation
```

Environment variables: `SODP_JWT_SECRET`, `SODP_JWT_PUBLIC_KEY_FILE`, `SODP_ACL_FILE`, `SODP_HEALTH_PORT`, `SODP_METRICS_PORT`, `SODP_RATE_WRITES_PER_SEC`, `SODP_BACKPRESSURE_LIMIT`, `SODP_REDIS_URL`.

### Go server (embedded library)

```bash
go get github.com/orkestri/sodp-go
```

```go
import sodp "github.com/orkestri/sodp-go"

srv := sodp.NewServer(
    sodp.WithJWTSecret([]byte(os.Getenv("SODP_JWT_SECRET"))),
    sodp.WithACLFile("config/acl.json"),
    sodp.WithPersistenceDir("/var/lib/sodp"),
    sodp.WithBackpressureLimit(1024),
)
defer srv.Close()

http.HandleFunc("/sodp", srv.HandleWS)

// Push state from server-side code
srv.Mutate("game.score", map[string]any{"value": 42})
srv.MutateAppend("game.events", event, 500) // append + cap array
srv.MutateDelete("game.player")
```

---

## Step 4 — ACL (access control)

Create `config/acl.json`:
```json
[
  { "pattern": "user.{sub}.*", "read": ["{sub}"],      "write": ["{sub}"] },
  { "pattern": "public.*",     "read": ["*"],            "write": ["role:editor"] },
  { "pattern": "admin.*",      "read": ["role:admin"],   "write": ["role:admin"] }
]
```

Pattern tokens: `{sub}` captures JWT `sub`; `*` matches remaining segments.
Permission values: `"*"` (anyone), `"{sub}"` (own), `"role:X"`, `"group:X"`, `"perm:X"`.

---

## Step 5 — Schema validation

Create `config/schema.json`:
```json
{
  "game.player": {
    "type": "Object",
    "fields": {
      "name":   { "type": "String" },
      "health": { "type": "Int" },
      "score":  { "type": "Float" },
      "position": {
        "type": "Object",
        "fields": {
          "x": { "type": "Float" },
          "y": { "type": "Float" }
        }
      }
    }
  }
}
```

Types: `String`, `Int`, `Float`, `Bool`, `Object`, `Array`, `Any`. Add `"nullable": true` to allow null. Unknown keys pass through (permissive). Invalid writes receive `ERROR 422`.

---

## Key concepts to explain to the user

- **WatchMeta.source** — `"cache"` (replayed from local store), `"init"` (server snapshot), `"delta"` (live mutation). Use `source === "init"` to distinguish the initial load from subsequent changes.
- **WatchMeta.initialized** — `false` if the key has never been written. Use this to detect a key that doesn't exist yet and initialize it.
- **Presence** — no cleanup needed. The server removes the entry and notifies all watchers when the session disconnects.
- **RESUME** — on reconnect, the server replays missed deltas. Clients never need to re-fetch.
- **Delta semantics** — only changed fields are sent to watchers. A mutation to 1 of 100 fields sends a 1-field delta.

---

## Resources

- GitHub: https://github.com/orkestri/SODP
- TypeScript client: https://www.npmjs.com/package/@sodp/client
- React hooks: https://www.npmjs.com/package/@sodp/react
- Python client: https://pypi.org/project/sodp-client/
- Java client: https://central.sonatype.com/artifact/site.orkestri/sodp-client
- Claude Code skills: https://github.com/orkestri/sodp-skills
