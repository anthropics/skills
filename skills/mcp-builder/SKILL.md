---
name: mcp-builder
description: Technical specification for architecting, implementing, testing, and evaluating Model Context Protocol (MCP) servers in TypeScript (MCP SDK) and Python (FastMCP).
license: Complete terms in LICENSE.txt
---

# MCP Server Development Specification

## Reference Resource Routing

Load each reference specification at the designated execution phase via `WebFetch` or local file ingestion:
- Protocol architecture, transport mechanisms, and primitive definitions (`Phase 1`):
  + Index sitemap ➔ `https://modelcontextprotocol.io/sitemap.xml`
  + Markdown specification page ➔ `https://modelcontextprotocol.io/specification/draft.md`
- Universal implementation standards (`Phase 1`, `Phase 2`):
  + Naming, formatting, pagination, transport, and security rules ➔ `./reference/mcp_best_practices.md`
- TypeScript runtime documentation (`Phase 1`, `Phase 2`):
  + SDK README ➔ `https://raw.githubusercontent.com/modelcontextprotocol/typescript-sdk/main/README.md`
  + Project structure, Zod schemas, and `server.registerTool` patterns ➔ `./reference/node_mcp_server.md`
- Python runtime documentation (`Phase 1`, `Phase 2`):
  + SDK README ➔ `https://raw.githubusercontent.com/modelcontextprotocol/python-sdk/main/README.md`
  + Module organization, Pydantic models, and `@mcp.tool` patterns ➔ `./reference/python_mcp_server.md`
- Evaluation benchmark specification (`Phase 4`):
  + Question generation, verification, and XML schema rules ➔ `./reference/evaluation.md`

## Phase 1: Architecture and Protocol Planning

### Service API Analysis
Extract endpoint definitions, authentication schemes, data models, and rate limits from the target service API documentation via web search and `WebFetch`.

### Tool Granularity and Naming
- Expose atomic API endpoints as primary composable tools and implement multi-step workflow tools for composite domain operations.
- Assign each tool a snake_case identifier prefixed with the target service name and an action verb:
  + GitHub issue creation endpoint ➔ `github_create_issue`
  + GitHub repository listing endpoint ➔ `github_list_repos`

### Context Filtering and Error Recovery
- Filter and paginate tool responses to return scoped data subsets matching the query parameters.
- Construct error responses containing the failure cause, rejected parameter values, and remediation steps for the calling agent.

### Runtime and Transport Selection
- Select the implementation stack and transport mechanism based on the execution environment:
  + Default implementation language ➔ TypeScript (`MCP SDK`)
  + Python implementation stack ➔ Python (`FastMCP`)
  + Remote server deployment ➔ Streamable HTTP with stateless JSON
  + Local process execution ➔ `stdio`
- Append the `.md` extension to specification URLs fetched from `https://modelcontextprotocol.io/sitemap.xml`:
  + Specification draft URL ➔ `https://modelcontextprotocol.io/specification/draft.md`

## Phase 2: Server Implementation

### Project Scaffolding and Core Infrastructure
- Initialize project configuration files (`package.json` and `tsconfig.json` for TypeScript; module dependencies for Python) according to the selected language guide (`./reference/node_mcp_server.md` or `./reference/python_mcp_server.md`).
- Consolidate shared execution logic into reusable infrastructure modules covering authenticated API clients, error formatters, JSON/Markdown serializers, and pagination handlers.

### Tool Schema and Registration
- Validate input parameters using `Zod` (TypeScript) or `Pydantic` (Python) with explicit type constraints, field descriptions, and inline value examples.
- Define `outputSchema` for structured responses and populate `structuredContent` alongside text output in the tool response payload.
- Document each registered tool with a functional summary, input parameter specifications, and return payload structure.
- Execute I/O operations asynchronously using `async`/`await` with pagination parameters and structured error recovery.
- Assign boolean behavioral annotations (`true` or `false`) to each tool definition based on operational state impact:
  + State-preserving data retrieval operation ➔ `readOnlyHint: true`
  + State-mutating or deleting operation ➔ `destructiveHint: true`
  + Repeatable operation yielding identical state ➔ `idempotentHint: true`
  + External network or third-party system interaction ➔ `openWorldHint: true`

## Phase 3: Verification and Static Analysis

### Codebase Audit
Verify single-source utility reuse, uniform error recovery patterns, explicit static type annotations across parameters and return values, and deterministic tool descriptions.

### Build and Interactive Inspection
Compile the server codebase and validate tool execution through the MCP Inspector:
- TypeScript build verification ➔ `npm run build`
- Python syntax verification ➔ `python -m py_compile your_server.py`
- Interactive protocol inspection ➔ `npx @modelcontextprotocol/inspector`

## Phase 4: Evaluation Suite Construction

### Benchmark Generation Workflow
Construct 10 evaluation question-answer pairs in accordance with `./reference/evaluation.md` across 4 sequential steps:
1. Inspect registered server tools to map available input parameters and query capabilities.
2. Execute read-only tool calls (`readOnlyHint: true`) against the target service to inspect live data records.
3. Formulate 10 realistic multi-step domain questions requiring sequential tool calls and cross-record synthesis.
4. Execute the tool call sequence for each question to verify the ground-truth answer prior to recording.

### Question Constraints
Enforce 6 structural properties on each evaluation item:
- Isolate each question as an independent execution unit decoupled from prior question states.
- Restrict tool invocations to state-preserving read operations (`readOnlyHint: true`).
- Require multi-step tool composition and cross-endpoint data exploration per question.
- Ground each question in practical domain workflows.
- Express each target answer as a single deterministic string verifiable via exact string comparison.
- Anchor each question and answer to fixed historical records or static data snapshots.

### Evaluation Output Schema
Export the verified evaluation suite in the following XML format:

```xml
<evaluation>
  <qa_pair>
    <question>Find discussions about AI model launches with animal codenames. One model needed a specific safety designation that uses the format ASL-X. What number X was being determined for the model named after a spotted wild cat?</question>
    <answer>3</answer>
  </qa_pair>
</evaluation>
```
