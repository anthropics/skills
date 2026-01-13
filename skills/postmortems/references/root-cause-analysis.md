# Root Cause Analysis Techniques

## 5 Whys

Guide users through iterative "why" questions to dig deeper into root causes.

**Example interaction:**
- User: "The service failed"
- AI: "Why did the service fail?"
- User: "Database connection timeout"
- AI: "Why did the connection timeout?"
- User: "Connection pool exhausted"
- AI: "Why was the pool exhausted?"
- ... (continues until root cause)

Continue asking "why" until reaching a root cause that cannot be further decomposed or points to a systemic issue.

## Causal Chain

Help users build a chain of causation from symptom to root cause:

```
Symptom → Immediate Cause → Contributing Factor → Root Cause
```

Guide users to identify each link in the chain and understand how they connect.

## Systems Thinking

Prompt users to consider multiple layers:

- **Technical**: Code, infrastructure, configuration
- **Process**: Deployment, monitoring, on-call procedures
- **Organizational**: Training, documentation, communication

For each layer, ask: "What gaps or issues exist at this level that contributed to the incident?"

## Blameless Reframing

When users provide information that blames individuals, help reframe in blameless terms:

- ❌ "John deployed the buggy code"
- ✅ "The deployment process allowed code without sufficient tests to reach production"

Always ask: "Why did the system/process allow this?" rather than "Why did this person do this?"
