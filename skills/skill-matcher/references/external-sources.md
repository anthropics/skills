# External Skill Sources

Reference for finding and installing skills from external catalogs when local skills don't match user needs.

## Official Sources

### Anthropic Skills Repository
**URL**: https://github.com/anthropics/skills
**Type**: Official skill library from Anthropic
**How to install**:
```bash
# Add marketplace (one-time)
claude plugin marketplace add anthropics/skills

# Install specific plugin sets
claude plugin install document-skills@anthropic-agent-skills
claude plugin install example-skills@anthropic-agent-skills
```

### Claude Skills via API
**URL**: https://claude.com/blog/extending-claude-capabilities-with-skills-mcp-servers
**Type**: Skills available in Claude.ai for paid plans
**Note**: These are automatically available in Claude.ai web interface

---

## Community Sources

### MCP Servers Directory
**URL**: https://mcpservers.org
**Type**: Community-maintained MCP server catalog
**Search**: Browse by category or search by functionality

### MCP Market
**URL**: https://mcpmarket.com
**Type**: MCP tools and skills marketplace
**Features**: Skill workflows, tutorials, examples

### Awesome MCP Servers
**URL**: https://github.com/punkpeye/awesome-mcp-servers
**Type**: Curated list of MCP servers
**Categories**: AI tools, development, productivity

---

## Installation Commands

### Add a marketplace
```bash
claude plugin marketplace add <owner>/<repo>
```

### List available plugins from marketplace
```bash
claude plugin marketplace list
```

### Install a plugin
```bash
claude plugin install <plugin-name>@<marketplace-name>
```

### List installed plugins
```bash
claude plugin list
```

### Remove a plugin
```bash
claude plugin uninstall <plugin-name>
```

---

## Search Strategy

When local skills don't match user needs:

1. **Search official repo first**
   - Check https://github.com/anthropics/skills/tree/main/skills
   - Look for matching skill names or descriptions

2. **Search MCP directories**
   - Use https://mcpservers.org search
   - Check category pages relevant to user's task

3. **Web search for specific needs**
   - Query: "claude code skill [task] site:github.com"
   - Query: "mcp server [functionality]"

4. **Suggest creating custom skill**
   - If no existing skill matches, recommend using skill-creator
   - Help user design a custom skill for their workflow

---

## Skill Quality Indicators

When recommending external skills, consider:

| Indicator | Good Sign | Warning Sign |
|-----------|-----------|--------------|
| Stars | 100+ stars | < 10 stars |
| Updates | Recent commits | No updates > 6 months |
| Documentation | Clear SKILL.md | Missing docs |
| Source | anthropics/ org | Unknown author |
| License | Apache 2.0, MIT | No license |

---

## Common External Skills by Category

### Data & Analytics
- BigQuery skills
- Database connectors
- Data visualization

### Cloud & DevOps
- AWS deployment
- Docker management
- CI/CD workflows

### Productivity
- Calendar integration
- Note-taking
- Task management

### Communication
- Email drafting
- Social media
- Translation

For specific needs not covered by installed skills, search external sources and recommend installation.
