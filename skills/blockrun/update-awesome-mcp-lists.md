---
name: update-awesome-mcp
description: Update BlockRun's awesome MCP server lists. Use /update-awesome-mcp to search for new MCP servers and update all managed repos.
---

# Update Awesome MCP Lists

批量更新 BlockRun 管理的 awesome MCP 列表。

## 管理的仓库

| Category | Repo | Topics |
|----------|------|--------|
| Finance | BlockRunAI/awesome-finance-mcp | stocks, crypto, DeFi, payments |
| DevOps | BlockRunAI/awesome-devops-mcp | AWS, GCP, Azure, K8s, CI/CD |
| Productivity | BlockRunAI/awesome-productivity-mcp | Notion, Slack, Calendar, email |
| Marketing | BlockRunAI/awesome-marketing-mcp | SEO, social media, analytics |
| E-commerce | BlockRunAI/awesome-ecommerce-mcp | Shopify, Amazon, payments |
| Data | BlockRunAI/awesome-data-mcp | Snowflake, BigQuery, ETL, BI |
| AI | BlockRunAI/awesome-ai-mcp | LLM, vector DB, image gen |
| Research | BlockRunAI/awesome-research-mcp | arXiv, PubMed, patents |
| Creator | BlockRunAI/awesome-creator-mcp | video, audio, design |
| Sales | BlockRunAI/awesome-sales-mcp | CRM, sales automation |
| Healthcare | BlockRunAI/awesome-healthcare-mcp | EHR, FHIR, clinical |

## 更新流程

### Step 1: 克隆所有仓库到 /tmp

```bash
CATEGORIES=("finance" "devops" "productivity" "marketing" "ecommerce" "data" "ai" "research" "creator" "sales" "healthcare")
for cat in "${CATEGORIES[@]}"; do
  gh repo clone BlockRunAI/awesome-${cat}-mcp /tmp/awesome-${cat}-mcp 2>/dev/null || (cd /tmp/awesome-${cat}-mcp && git pull)
done
```

### Step 2: 搜索新的 MCP servers

数据来源：
1. **GitHub 搜索**: `gh search repos "mcp server {topic}" --limit 50`
2. **主列表**: https://github.com/punkpeye/awesome-mcp-servers
3. **官方**: https://github.com/modelcontextprotocol/servers
4. **目录**: https://mcp.so, https://glama.ai/mcp/servers

### Step 3: 验证每个 server

- [ ] 是真正的 MCP server？(有 mcp.json 或用 MCP SDK)
- [ ] 活跃维护？(6个月内有 commit)
- [ ] 有文档？
- [ ] 不在现有列表中？

### Step 4: 条目格式

```markdown
| [Server Name](url) | 简短描述 (≤80字符) | ![Stars](https://img.shields.io/github/stars/owner/repo) |
```

### Step 5: 提交推送

```bash
cd /tmp/awesome-{category}-mcp
git add README.md
git commit -m "Update {category} MCP servers - $(date +%Y-%m-%d)"
git push
```

## GitHub Topics (Tags) 管理

每个仓库需要设置正确的 GitHub Topics 来提高可发现性。

### 设置 Topics 命令

```bash
gh repo edit BlockRunAI/awesome-{category}-mcp --add-topic "mcp,mcp-servers,awesome-list,{category-specific-topics}"
```

### 各仓库推荐 Topics

| Category | Topics |
|----------|--------|
| Finance | `mcp`, `mcp-servers`, `awesome-list`, `finance`, `cryptocurrency`, `defi`, `trading`, `payments` |
| DevOps | `mcp`, `mcp-servers`, `awesome-list`, `devops`, `aws`, `kubernetes`, `docker`, `cicd`, `cloud` |
| Productivity | `mcp`, `mcp-servers`, `awesome-list`, `productivity`, `notion`, `slack`, `calendar`, `automation` |
| Marketing | `mcp`, `mcp-servers`, `awesome-list`, `marketing`, `seo`, `analytics`, `social-media` |
| E-commerce | `mcp`, `mcp-servers`, `awesome-list`, `ecommerce`, `shopify`, `payments`, `inventory` |
| Data | `mcp`, `mcp-servers`, `awesome-list`, `data`, `database`, `etl`, `bigquery`, `snowflake` |
| AI | `mcp`, `mcp-servers`, `awesome-list`, `ai`, `llm`, `machine-learning`, `vector-database` |
| Research | `mcp`, `mcp-servers`, `awesome-list`, `research`, `arxiv`, `academic`, `papers` |
| Creator | `mcp`, `mcp-servers`, `awesome-list`, `creator`, `video`, `design`, `content-creation` |
| Sales | `mcp`, `mcp-servers`, `awesome-list`, `sales`, `crm`, `salesforce`, `lead-generation` |
| Healthcare | `mcp`, `mcp-servers`, `awesome-list`, `healthcare`, `fhir`, `ehr`, `medical` |

### 批量设置 Topics 脚本

```bash
#!/bin/bash
gh repo edit BlockRunAI/awesome-finance-mcp --add-topic "mcp,mcp-servers,awesome-list,finance,cryptocurrency,defi,trading,payments"
gh repo edit BlockRunAI/awesome-devops-mcp --add-topic "mcp,mcp-servers,awesome-list,devops,aws,kubernetes,docker,cicd,cloud"
gh repo edit BlockRunAI/awesome-productivity-mcp --add-topic "mcp,mcp-servers,awesome-list,productivity,notion,slack,calendar,automation"
gh repo edit BlockRunAI/awesome-marketing-mcp --add-topic "mcp,mcp-servers,awesome-list,marketing,seo,analytics,social-media"
gh repo edit BlockRunAI/awesome-ecommerce-mcp --add-topic "mcp,mcp-servers,awesome-list,ecommerce,shopify,payments,inventory"
gh repo edit BlockRunAI/awesome-data-mcp --add-topic "mcp,mcp-servers,awesome-list,data,database,etl,bigquery,snowflake"
gh repo edit BlockRunAI/awesome-ai-mcp --add-topic "mcp,mcp-servers,awesome-list,ai,llm,machine-learning,vector-database"
gh repo edit BlockRunAI/awesome-research-mcp --add-topic "mcp,mcp-servers,awesome-list,research,arxiv,academic,papers"
gh repo edit BlockRunAI/awesome-creator-mcp --add-topic "mcp,mcp-servers,awesome-list,creator,video,design,content-creation"
gh repo edit BlockRunAI/awesome-sales-mcp --add-topic "mcp,mcp-servers,awesome-list,sales,crm,salesforce,lead-generation"
gh repo edit BlockRunAI/awesome-healthcare-mcp --add-topic "mcp,mcp-servers,awesome-list,healthcare,fhir,ehr,medical"
```

## 搜索关键词

| Category | Search Terms |
|----------|-------------|
| Finance | stocks, trading, cryptocurrency, defi, payments, banking |
| DevOps | aws, kubernetes, docker, terraform, cicd, gcp, azure |
| Productivity | notion, slack, calendar, email, todoist, trello |
| Marketing | seo, analytics, social media, mailchimp, hubspot |
| E-commerce | shopify, stripe, amazon, woocommerce, inventory |
| Data | snowflake, bigquery, postgresql, mongodb, etl, dbt |
| AI | openai, anthropic, vector database, pinecone, langchain |
| Research | arxiv, pubmed, academic, papers, scholar |
| Creator | youtube, video, figma, canva, audio, podcast |
| Sales | salesforce, crm, hubspot, pipedrive, leads |
| Healthcare | healthcare, fhir, ehr, medical, health |

## 质量标准

1. **Stars**: 优先 10+ stars
2. **活跃**: 6个月内有更新
3. **文档**: 必须有 README
4. **可用**: 检查 issues 没有重大 bug
5. **无重复**: 添加前检查现有条目

## 执行更新

当用户说 "update awesome lists" 或 "/update-awesome-mcp":

1. 问用户要更新哪些 category (全部 or 指定)
2. Clone/pull 对应的 repos
3. 搜索新的 MCP servers
4. 展示找到的新条目让用户确认
5. 更新 README.md
6. 设置/更新 GitHub Topics
7. Commit 并 push
