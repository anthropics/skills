# Healthcare Tools Quick Start

## 🏥 Available Tools at a Glance

| Tool | Type | Purpose | Command |
|------|------|---------|---------|
| **CMS Coverage** | MCP Server | Medicare coverage policies | Query via MCP |
| **ICD-10 Codes** | MCP Server | Medical coding database | Query via MCP |
| **NPI Registry** | MCP Server | Healthcare provider lookup | Query via MCP |
| **PubMed** | MCP Server | Biomedical literature | Query via MCP |
| **Clinical Trial Protocol** | Skill | Generate FDA-compliant protocols | `/clinical-trial-protocol` |
| **Prior Auth Review** | Skill | Analyze prior authorization | `/prior-auth-review` |
| **FHIR Developer** | Skill | Build FHIR APIs | `/fhir-developer` |

## ⚡ Quick Start Examples

### Find Medicare Coverage
```
"What's the Medicare coverage policy for cataract surgery?"
"Show me the NCD for diabetic complications"
```

### Look Up Medical Codes
```
"Find the ICD-10 code for acute myocardial infarction"
"What's the procedure code for knee arthroscopy?"
```

### Find Healthcare Providers
```
"Search NPI registry for cardiologists in Boston"
"Verify provider credentials for NPI 1234567890"
```

### Search Medical Literature
```
"Find recent PubMed studies on gene therapy"
"Get the full text of PMID 12345678"
```

### Generate Clinical Protocols
```
/clinical-trial-protocol
Create a Phase II oncology trial protocol
```

### Analyze Prior Authorizations
```
/prior-auth-review
Review this prior auth for spinal fusion surgery
```

### Build FHIR Endpoints
```
/fhir-developer
Show me how to implement FHIR patient search
```

## 🔧 Configuration Files

### `.mcp.json` - MCP Server Configuration
Defines HTTP endpoints for healthcare data sources.

### `.claude/settings.json` - Project Settings
- Healthcare plugin marketplace
- Enabled skills (clinical-trial-protocol, prior-auth-review, fhir-developer)
- Permission rules for healthcare operations
- Environment variables for API timeouts

### `.claude/HEALTHCARE.md` - Full Documentation
Complete guide with use cases, security, and troubleshooting.

## 🚀 First Time Setup

1. **Restart Claude Code** to load new configurations
2. **Test a query**: "Search PubMed for recent cardiology studies"
3. **Explore skills**: Try `/clinical-trial-protocol` or `/fhir-developer`
4. **Configure credentials**: Add API keys to environment if needed

## 📖 Learn More

- **Full Guide**: See `.claude/HEALTHCARE.md`
- **MCP Servers**: Detailed use cases and examples
- **Skills**: Complete documentation and workflows
- **Security**: Permission rules and best practices

## 🆘 Need Help?

| Issue | Solution |
|-------|----------|
| MCP server not responding | Check internet connection, restart Claude Code |
| Skill not found | Reload plugin cache, verify healthcare marketplace |
| Permission denied | Review `.claude/settings.json` permission rules |
| API timeout | Increase `HEALTHCARE_API_TIMEOUT` environment variable |

---

**Pro Tip**: Use `/fhir-developer` to learn FHIR standards while building APIs!

For detailed information, see `.claude/HEALTHCARE.md`
