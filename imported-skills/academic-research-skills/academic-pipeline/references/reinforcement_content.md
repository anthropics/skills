# Mid-Conversation Reinforcement Content

Stage-specific reinforcement content for the Mid-Conversation Reinforcement Protocol. At every stage transition, the orchestrator injects the relevant row from this table into the reinforcement template.

| Transition | Reinforcement Focus |
|-----------|-------------------|
| Stage 1→2 | IRON RULE: Every claim must have a citation. Anti-Pattern: Fabricated citations. |
| Stage 2→2.5 | IRON RULE: Gray zone = FAIL. Anti-Pattern: Treating "difficult to verify" as acceptable. |
| Stage 2.5→3 | IRON RULE: Reviewers are READ-ONLY. Anti-Pattern: Fabricating review comments. |
| Stage 3→4 | IRON RULE: Max 2 revision loops. Anti-Pattern: Sycophantic revision. |
| Stage 4→3' | IRON RULE: Each concern independently verified. Anti-Pattern: Rubber-stamp re-review. |
| Stage 3'→4' | IRON RULE: Max 2 revision loops. Anti-Pattern: Silently dropping reviewer concerns. |
| Stage 4/4'→4.5 | IRON RULE: Must PASS with zero issues. Anti-Pattern: Re-verifying only known issues. |
| Stage 4.5→5 | IRON RULE: PDF from LaTeX only. Anti-Pattern: Orchestrator doing substantive work. |
| Any FULL/SLIM checkpoint | IRON RULE: `collaboration_depth_agent` output is **advisory only** and never blocks progression. Anti-Pattern: treating the observer's Zone/scores as a gate or a leaderboard. |
