# Root Cause Analysis Techniques

## Approach

Analyze root causes based on information provided in the conversation. You can synthesize information from multiple messages, ask clarifying questions when needed, and provide analysis proactively rather than requiring strict question-answer sequences.

## 5 Whys

Use iterative "why" questions to dig deeper into root causes. You can:

- **Analyze from conversation**: If the user has already provided information about what happened, analyze it and identify the chain of "whys" yourself
- **Ask when needed**: Only ask "why" questions if information is missing or unclear
- **Present the chain**: Show the full 5 Whys chain once you have enough information

**Example:**
If user says "The service failed because database connection timed out", you can analyze:
1. Why did the service fail? → Database connection timeout
2. Why did the connection timeout? → Connection pool exhausted (infer or ask if unclear)
3. Why was the pool exhausted? → Long-running queries blocking connections (infer or ask)
4. Why were there long-running queries? → Missing index on frequently queried column (infer or ask)
5. Why was the index missing? → Database migration script didn't include index creation (root cause)

Present this analysis and ask for confirmation or clarification if needed.

## Causal Chain

Build a chain of causation from symptom to root cause based on available information:

```
Symptom → Immediate Cause → Contributing Factor → Root Cause
```

Identify each link from the conversation context. If a link is unclear, ask a specific question about that link rather than going through the whole chain step-by-step.

## Systems Thinking

Analyze across multiple layers based on what the user has shared:

- **Technical**: Code, infrastructure, configuration
- **Process**: Deployment, monitoring, on-call procedures
- **Organizational**: Training, documentation, communication

For each layer, identify gaps or issues that contributed to the incident. If information is missing for a layer, ask targeted questions about that specific layer.

## Blameless Reframing

When users provide information that blames individuals, automatically reframe in blameless terms:

- ❌ "John deployed the buggy code"
- ✅ "The deployment process allowed code without sufficient tests to reach production"

Always frame causes in terms of systems and processes, not individuals. Ask: "Why did the system/process allow this?" rather than "Why did this person do this?"

## Analysis Workflow

1. **Synthesize available information**: Review what the user has shared about the incident
2. **Identify gaps**: Determine what information is missing for a complete root cause analysis
3. **Ask targeted questions**: Only ask about specific gaps, not the entire chain
4. **Present analysis**: Show your root cause analysis and causal chain
5. **Validate and refine**: Ask if the analysis makes sense or if anything is missing
