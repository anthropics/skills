# Healthcare Integration Guide

This project is configured with comprehensive healthcare tools and resources for clinical, regulatory, and FHIR development workflows.

## 🏥 MCP Servers

### 1. CMS Coverage Database
**Purpose**: Access Medicare Part B coverage policies including NCDs (National Coverage Determinations) and LCDs (Local Coverage Determinations).

**Endpoint**: `https://mcp.deepsense.ai/cms_coverage/mcp`

**Use Cases**:
- Look up Medicare coverage policies for procedures
- Check coverage criteria for specific treatments
- Verify billing and coding requirements
- Research coverage determinations by region

**Example Usage**:
```
"Find the Medicare coverage policy for cardiac imaging with PET scans"
"What are the coverage requirements for gene therapy treatments?"
"Show me the LCD for orthopedic procedures in region X"
```

---

### 2. ICD-10 Codes
**Purpose**: Access complete ICD-10-CM (diagnosis) and ICD-10-PCS (procedure) code sets for medical classification and billing.

**Endpoint**: `https://mcp.deepsense.ai/icd10_codes/mcp`

**Use Cases**:
- Find correct ICD-10 codes for diagnoses and procedures
- Validate billing and coding accuracy
- Research code hierarchies and relationships
- Support medical record documentation

**Example Usage**:
```
"Find the ICD-10 code for Type 2 diabetes with complications"
"What's the correct code for laparoscopic cholecystectomy?"
"Show me all cardiovascular procedure codes"
```

---

### 3. NPI Registry
**Purpose**: Query the US National Provider Identifier (NPI) Registry containing information about HIPAA-covered healthcare providers.

**Endpoint**: `https://mcp.deepsense.ai/npi_registry/mcp`

**Use Cases**:
- Look up provider credentials and qualifications
- Verify provider information and specialties
- Research provider networks and affiliations
- Validate provider licensing and certifications

**Example Usage**:
```
"Find providers with NPI matching 'cardiologist' in New York"
"Verify the credentials for provider with NPI XXXXXXXXXX"
"Show all specialists in the XYZ hospital network"
```

---

### 4. PubMed
**Purpose**: Search biomedical literature, access citations, abstracts, and full-text articles from PubMed and PubMed Central.

**Endpoint**: `https://pubmed.mcp.claude.com/mcp`

**Use Cases**:
- Literature reviews for clinical research
- Evidence-based medicine lookups
- Research article discovery and retrieval
- Citation and metadata access

**Example Usage**:
```
"Search PubMed for recent studies on immunotherapy in oncology"
"Find the latest guidelines on hypertension management"
"Get the full text of this PMID: 12345678"
```

---

## 🛠️ Healthcare Skills

### 1. Clinical Trial Protocol Generator
**Skill**: `clinical-trial-protocol@healthcare`

**Purpose**: Generate FDA/NIH-compliant clinical trial protocols for medical devices or drugs.

**Capabilities**:
- Create study designs (RCT, observational, etc.)
- Generate regulatory-compliant documentation
- Define inclusion/exclusion criteria
- Specify safety monitoring protocols
- Create informed consent templates

**Configuration**:
- `regulatory_framework`: FDA (default) or EMA
- `protocol_template`: standard, adaptive, or basket

**Example Usage**:
```
/clinical-trial-protocol
Generate a Phase III RCT protocol for a new cardiovascular drug
```

---

### 2. Prior Authorization Review Tool
**Skill**: `prior-auth-review@healthcare`

**Purpose**: Automate payer review of prior authorization requests with clinical documentation synthesis.

**Capabilities**:
- Analyze medical necessity documentation
- Verify coverage eligibility
- Generate authorization summaries
- Identify documentation gaps
- Create appeal templates

**Configuration**:
- `payer_type`: commercial, medicare, medicaid, or all

**Example Usage**:
```
/prior-auth-review
Review this prior auth request for orthopedic surgery
```

---

### 3. FHIR API Developer Guide
**Skill**: `fhir-developer@healthcare`

**Purpose**: Build healthcare endpoints with FHIR R4 resources and SMART on FHIR authorization.

**Capabilities**:
- FHIR resource definitions and examples
- SMART on FHIR OAuth implementation
- Data interchange patterns
- Validation and testing guidance
- Compliance and security best practices

**Configuration**:
- `fhir_version`: R4 (default), STU3, or DSTU2
- `enable_smart_auth`: true (default) for SMART on FHIR

**Example Usage**:
```
/fhir-developer
Show me how to implement a patient search endpoint using FHIR R4
```

---

## 🔐 Security & Permissions

### Healthcare-Specific Permissions
```json
{
  "allow": [
    "Read",           // Read healthcare documents
    "Glob",           // Find healthcare files
    "Grep",           // Search healthcare content
    "WebFetch(*.cms.gov/*)",        // CMS official resources
    "WebFetch(pubmed.ncbi.nlm.nih.gov/*)",  // PubMed access
    "WebFetch(fhir.hl7.org/*)"      // FHIR standards
  ],
  "ask": [
    "Write",          // Prompt before modifying files
    "Edit"            // Prompt before editing files
  ]
}
```

### Environment Configuration
```env
HEALTHCARE_API_TIMEOUT=30000        # API timeout in milliseconds
FHIR_VERSION=R4                     # Default FHIR version
CMS_API_RETRIES=3                   # Retry attempts for CMS API
```

---

## 📋 Workflow Examples

### Example 1: Clinical Trial Setup
1. Use **Clinical Trial Protocol** skill to generate protocol outline
2. Reference **PubMed** for literature review of similar studies
3. Check **CMS Coverage** for reimbursement implications
4. Use **FHIR Developer** guide for data collection implementation

### Example 2: Prior Authorization
1. Use **Prior Auth Review** skill to analyze request
2. Look up **ICD-10 Codes** for correct medical coding
3. Check **CMS Coverage** for coverage determination
4. Reference **PubMed** for clinical evidence

### Example 3: FHIR Implementation
1. Use **FHIR Developer** guide for API design
2. Reference **NPI Registry** for provider lookup patterns
3. Check **ICD-10 Codes** for coding system integration
4. Review **PubMed** for interoperability standards

---

## 🚀 Getting Started

### Setup Verification
```bash
# Verify MCP servers are configured
cat .mcp.json | jq '.mcpServers | keys'

# Verify healthcare skills are enabled
cat .claude/settings.json | jq '.enabledPlugins | keys'
```

### First Steps
1. **Reload Claude Code** - Restart to load new MCP servers and skills
2. **Test MCP Servers** - Query each server to verify connectivity
3. **Explore Skills** - Try out each healthcare skill with sample requests
4. **Configure API Keys** - Add any required credentials to environment variables

---

## 📚 Additional Resources

### Official Standards
- [FHIR R4 Specification](https://www.hl7.org/fhir/R4/)
- [SMART on FHIR](http://docs.smarthealthit.org/)
- [ICD-10-CM Official Guidelines](https://www.cdc.gov/nchs/icd/icd-10-cm.htm)

### Healthcare Integration
- [CMS.gov Official Site](https://www.cms.gov/)
- [PubMed](https://pubmed.ncbi.nlm.nih.gov/)
- [NPI Registry](https://npiregistry.cms.hhs.gov/)

### Best Practices
- Always verify regulatory compliance requirements
- Use official source materials for clinical guidance
- Document all medical and regulatory decisions
- Follow HIPAA guidelines when handling PHI

---

## ⚙️ Troubleshooting

### MCP Server Connection Issues
- Verify internet connectivity
- Check that `enableAllProjectMcpServers` is set to `true`
- Ensure firewall allows outbound HTTPS connections
- Test individual servers with simple queries

### Skill Not Working
- Restart Claude Code to reload plugin cache
- Verify healthcare marketplace is properly configured
- Check that plugin is enabled in settings
- Review plugin-specific configuration options

### Permission Denied Errors
- Check `.claude/settings.json` permission rules
- Verify required domains are whitelisted
- Review environment variable configuration
- Ensure proper file access permissions

---

## 🔄 Updating Healthcare Tools

To update to the latest healthcare tools:
```bash
# Update the healthcare marketplace
# (This happens automatically on startup if autoUpdate is enabled)

# Manual update
git submodule update --remote
# or
npm update  # if using npm-based plugin management
```

---

## 📞 Support & Feedback

For issues or questions:
- Check the [healthcare repository](https://github.com/drsandeeprana00-bit/healthcare)
- Review individual skill documentation
- Consult official healthcare standards and APIs
- File issues in the skills repository

---

**Last Updated**: 2026-06-06
**Version**: 1.0
