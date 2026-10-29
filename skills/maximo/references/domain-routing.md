# MAXIMO domain routing

Route by the user's requested outcome, not by isolated keywords. A request can use more than one route, but keep the route list short and explicit.

| Route | Use for | Repository skills and checks |
| --- | --- | --- |
| Software engineering | code, debugging, architecture, tests, APIs, repositories, automation scripts | inspect project conventions; existing test/build/lint commands; `webapp-testing` for browser behavior |
| Finance and accounting | budgets, forecasts, reconciliations, management reporting, valuation, bookkeeping analysis | identify currency, period, accounting framework, and source records; show formulas and sensitivity |
| Legal and compliance | contracts, policies, regulatory research, rights and obligations | identify jurisdiction and effective date; use primary authorities; include professional-review boundary |
| Audit and controls | evidence review, control design, risk registers, audit workpapers | preserve evidence lineage; distinguish observation, criterion, risk, and recommendation; do not certify |
| Marketing and communications | positioning, campaigns, copy, research, launch plans, internal communications | label assumptions and generated claims; verify audience, brand, consent, and substantiation |
| Research and data analysis | literature or market research, datasets, statistics, dashboards, experiments | define question and population; cite sources; document transformations, missingness, and uncertainty |
| Documents and presentations | reports, proposals, specs, slides, PDFs, office files | compose `doc-coauthoring`, `docx`, `pdf`, `pptx`, or `xlsx`; render or validate output when supported |
| Design and web artifacts | visual systems, web pages, prototypes, charts, graphics | compose `frontend-design`, `canvas-design`, `theme-factory`, or `web-artifacts-builder`; test accessibility and responsive behavior when relevant |
| Integrations and operations | APIs, MCP servers, scheduled jobs, workflow automation | compose `mcp-builder` or `claude-api`; least privilege, dry runs, retries, and explicit destructive-action confirmation |

When no route fits, use general reasoning and say which assumptions make the result bounded. When a route conflicts with safety or authorization, safety wins.
