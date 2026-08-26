# procedure-coding

Assigns CPT and HCPCS Level II procedure codes from encounter documentation. Sibling to `icd10-cm` (which handles the diagnosis side).

## Connectors

- **HCPCS Level II** — uses the `hcpcs_codes` MCP connector (`search_codes`, `lookup_code`, `validate_code`, `list_codes`). Required for HCPCS-II coding; the skill will not propose Level II codes from memory.
- **CPT** — optionally uses a `cpt_codes` connector (`cpt_search_codes`, `cpt_lookup_code`) if one is configured. CPT descriptors are AMA-licensed, so no CPT data ships with this skill or its connector by default. Without the connector the skill proposes CPT codes from model knowledge and flags them as pending verification against the user's licensed CPT source — the same posture as the standalone `cpt` skill.

## Scope

Covers: E/M, procedures/surgery, lab/path, imaging, medicine services, HCPCS Level II supplies/devices/observation/screening services, and CPT Category II tracking codes (gated to quality-reporting context).

Does not cover: modifiers, NCCI bundling edits, MUE units, or payer-specific code substitutions — those depend on payer rules not present in the clinical documentation.
