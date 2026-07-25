# PRD Quality Checklist

Use this checklist to validate generated PRDs before delivery.

## Completeness

- [ ] Every route/page has a corresponding document
- [ ] All form fields listed with type, required, validation, default
- [ ] All table columns listed with format, sortable, filterable
- [ ] All action buttons documented with visibility conditions
- [ ] All API endpoints listed with method, path, trigger, params
- [ ] Mock vs integrated APIs clearly distinguished
- [ ] All enums exhaustively listed with every value
- [ ] Page load behavior documented for every page
- [ ] Page relationships mapped (inbound, outbound, data coupling)

## Accuracy

- [ ] Route paths match actual code
- [ ] Field names match UI labels (not variable names)
- [ ] Validation rules match actual code logic
- [ ] Permission conditions match auth guard implementations
- [ ] API paths match actual service layer calls
- [ ] Enum values match source constants (no fabrication)
- [ ] Uncertain items marked `[TBC]` with explanation

## Readability

- [ ] Business language used (not implementation details)
- [ ] Each page doc is self-contained
- [ ] No component names used as page names
- [ ] Interactions described as user action → system response
- [ ] Modals/drawers documented within their parent page
- [ ] README system overview written for non-technical reader

## Structure

- [ ] `prd/README.md` exists with system overview + page inventory
- [ ] `prd/pages/` contains numbered page files
- [ ] `prd/appendix/enum-dictionary.md` exists
- [ ] `prd/appendix/api-inventory.md` exists
- [ ] `prd/appendix/page-relationships.md` exists
- [ ] Cross-references use relative links

## Backend-Specific Checks

- [ ] All controller/view endpoints documented with method, path, auth
- [ ] DTO/serializer fields listed with type, required, validation
- [ ] Database model relationships mapped (FK, M2M, O2O)
- [ ] Django admin customizations documented (list_display, actions, inlines)
- [ ] Background tasks/Celery jobs documented with trigger and schedule
- [ ] Middleware pipeline documented (auth, logging, rate limiting)
- [ ] Environment-dependent behavior noted (dev vs prod differences)
- [ ] Database migrations reviewed for field constraints and defaults

## Common Issues to Watch

| Issue | How to Detect | Fix |
|-------|--------------|-----|
| Missing modal content | Search for `Modal`, `Dialog`, `Drawer` components | Add as subsection in parent page |
| Undocumented field linking | Search for conditional renders based on field values | Add to interaction logic |
| Hidden permissions | Search for `v-if`, `v-show`, role checks, auth guards | Add visibility conditions |
| Stale mock data | Compare mock shapes with API types/interfaces | Flag as `[Mock - verify with backend]` |
| Missing error states | Search for error boundaries, catch blocks, toast errors | Add failure paths to interactions |
| Unlinked pages | Cross-reference route params with navigation calls | Complete page relationships |
