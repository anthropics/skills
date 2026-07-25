# MCP Validation Checklist

## Structural Integrity
- [ ] Tool names are unique across the manifest
- [ ] Tool names use lowercase snake_case (3-64 chars, `[a-z0-9_]`)
- [ ] `inputSchema.type` is always `"object"`
- [ ] Every `required` field exists in `properties`
- [ ] No empty `properties` objects (warn if inputs truly optional)

## Descriptive Quality
- [ ] All tools include actionable descriptions (≥10 chars)
- [ ] Descriptions start with a verb ("Create…", "Retrieve…", "Delete…")
- [ ] Parameter descriptions explain expected values, not just types

## Security & Safety
- [ ] Auth tokens and secrets are NOT exposed in tool schemas
- [ ] Destructive tools require explicit confirmation input parameters
- [ ] No tool accepts arbitrary URLs or file paths without validation
- [ ] Outbound host allowlists are explicit where applicable

## Versioning & Compatibility
- [ ] Breaking tool changes use new tool IDs (never rename in-place)
- [ ] Additive-only changes for non-breaking updates
- [ ] Contract changelog is maintained per release
- [ ] Deprecated tools include sunset timeline in description

## Runtime & Error Handling
- [ ] Error responses use consistent structure (`code`, `message`, `details`)
- [ ] Timeout and rate-limit behaviors are documented
- [ ] Large response payloads are paginated or truncated
