# MCP Builder

## Description
This skill is a comprehensive guide and toolkit for developing high-quality Model Context Protocol (MCP) servers. It provides a structured workflow—from research and planning to implementation and evaluation—ensuring that the resulting servers are robust, agent-friendly, and compliant with MCP standards. It supports both Python (FastMCP) and Node/TypeScript SDKs, offering best practices, reference materials, and evaluation strategies to build tools that LLMs can effectively use to interact with external systems.

## Requirements
- **Core**: Knowledge of the MCP Protocol (available via WebFetch or provided references).
- **Python Dev**: Python 3.x, `mcp` SDK, `pydantic`.
- **Node Dev**: Node.js, TypeScript, `@modelcontextprotocol/sdk`, `zod`.
- **Reference Files**: Access to `reference/` directory (`mcp_best_practices.md`, `python_mcp_server.md`, etc.).

## Cautions
- **Blocking Processes**: MCP servers are long-running; do not run them directly in the main process during development (use tmux or timeouts).
- **Context Windows**: Optimize tool outputs for limited context windows; use concise formats.
- **Error Handling**: Ensure error messages are actionable for the agent, not just stack traces.
- **Security**: Validate all inputs using strict schemas (Pydantic/Zod).

## Definitions
- **MCP**: Model Context Protocol, a standard for connecting AI models to external data and tools.
- **Server**: An application that provides a list of tools/resources to an MCP client (the LLM).
- **Transport**: The communication channel (stdio, SSE) used by the protocol.
- **FastMCP**: A high-level Python framework for building MCP servers quickly.

## Log
(No run logs available yet. This section will be populated by the system upon successful execution.)

## Model Readme
To use this skill, follow the 4-Phase Workflow defined in `SKILL.md`:
1.  **Research**: Plan the tools based on agent workflows, not just API endpoints. Study the `reference/mcp_best_practices.md`.
2.  **Implementation**:
    -   For **Python**, refer to `reference/python_mcp_server.md`. Use the `mcp` package and Pydantic models.
    -   For **TypeScript**, refer to `reference/node_mcp_server.md`. Use `zod` for schemas.
3.  **Refine**: Ensure code quality, DRY principles, and proper error handling.
4.  **Evaluate**: Create an evaluation suite using `reference/evaluation.md` to verify the server's effectiveness with realistic queries.
