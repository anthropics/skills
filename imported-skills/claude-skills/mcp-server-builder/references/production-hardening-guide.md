# Production Hardening Guide — Safety, Versioning, Quality Gates

The advisory layer behind the mcp-server-builder workflows: read this when
hardening a scaffolded server for production, designing auth, planning
contract evolution, or reviewing a manifest before publishing.

## Auth & Safety Design

- Keep secrets in env, not in tool schemas.
- Prefer explicit allowlists for outbound hosts.
- Return structured errors (`code`, `message`, `details`) for agent recovery.
- Avoid destructive operations without explicit confirmation inputs.

## Versioning Strategy

- Additive fields only for non-breaking updates.
- Never rename tool names in-place.
- Introduce new tool IDs for breaking behavior changes.
- Maintain changelog of tool contracts per release.

## Common Pitfalls

1. Tool names derived directly from raw paths (`get__v1__users___id`)
2. Missing operation descriptions (agents choose tools poorly)
3. Ambiguous parameter schemas with no required fields
4. Mixing transport errors and domain errors in one opaque message
5. Building tool contracts that expose secret values
6. Breaking clients by changing schema keys without versioning

## Best Practices

1. Use `operationId` as canonical tool name when available.
2. Keep one task intent per tool; avoid mega-tools.
3. Add concise descriptions with action verbs.
4. Validate contracts in CI using strict mode.
5. Keep generated scaffold committed, then customize incrementally.
6. Pair contract changes with changelog entries.

## Architecture Decisions

Choose the server approach per constraint:

- Python runtime: faster iteration, data pipelines, backend-heavy teams
- TypeScript runtime: shared types with JS stack, frontend-heavy teams
- Single MCP server: easiest operations, broader blast radius
- Split domain servers: cleaner ownership and safer change boundaries

## Contract Quality Gates

Before publishing a manifest:

1. Every tool has clear verb-first name.
2. Every tool description explains intent and expected result.
3. Every required field is explicitly typed.
4. Destructive actions include confirmation parameters.
5. Error payload format is consistent across all tools.
6. Validator returns zero errors in strict mode.

## Testing Strategy

- Unit: validate transformation from OpenAPI operation to MCP tool schema.
- Contract: snapshot `tool_manifest.json` and review diffs in PR.
- Integration: call generated tool handlers against staging API.
- Resilience: simulate 4xx/5xx upstream errors and verify structured responses.

## Deployment Practices

- Pin MCP runtime dependencies per environment.
- Roll out server updates behind versioned endpoint/process.
- Keep backward compatibility for one release window minimum.
- Add changelog notes for new/removed/changed tool contracts.

## Security Controls

- Keep outbound host allowlist explicit.
- Do not proxy arbitrary URLs from user-provided input.
- Redact secrets and auth headers from logs.
- Rate-limit high-cost tools and add request timeouts.
