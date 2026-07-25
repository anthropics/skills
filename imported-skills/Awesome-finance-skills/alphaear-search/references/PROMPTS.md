# AlphaEar Search Prompts

## Search Cache Relevance (Smart Cache)

**Prompt:**

```markdown
Task: Decide if existing information from previous searches or local news is sufficient for the new search query.

New Query: "{current_query}"

Available Information Candidates:
{candidates_desc}

Instructions:
1. Analyze if any candidate provides ENOUGH up-to-date info for the "New Query".
2. If yes, choose the best one.
3. If the query implies needing LATEST real-time info and candidates are older than a few hours/days (depending on topic volatility), choose none.
4. Return strictly JSON: {"reuse": true/false, "index": <candidate_index_int>, "reason": "short explanation"}
```
