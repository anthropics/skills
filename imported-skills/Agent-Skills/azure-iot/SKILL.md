---
name: azure-iot
description: Expert knowledge for Azure IoT development including decision making. Use when designing Azure IoT device registries, namespaces, schema registries, data models, or device metadata structures, and other Azure IoT related development tasks. Not for Azure IoT Central (use azure-iot-central), Azure IoT Edge (use azure-iot-edge), Azure IoT Hub (use azure-iot-hub), Azure Defender For Iot (use azure-defender-for-iot).
compatibility: Requires network access. Uses mcp_microsoftdocs:microsoft_docs_fetch or fetch_webpage to retrieve documentation.
metadata:
  generated_at: "2026-07-12"
  generator: "docs2skills/1.0.0"
---
# Azure IoT Skill

This skill provides expert guidance for Azure IoT. Covers decision making. It combines local quick-reference content with remote documentation fetching capabilities.

## How to Use This Skill

> **IMPORTANT for Agent**: Use the **Category Index** below to locate relevant sections. For categories with line ranges (e.g., `L35-L120`), use `read_file` with the specified lines. For categories with file links (e.g., `[security.md](security.md)`), use `read_file` on the linked reference file

> **IMPORTANT for Agent**: If `metadata.generated_at` is more than 3 months old, suggest the user pull the latest version from the repository. If `mcp_microsoftdocs` tools are not available, suggest the user install it: [Installation Guide](https://github.com/MicrosoftDocs/mcp/blob/main/README.md)

This skill requires **network access** to fetch documentation content:
- **Preferred**: Use `mcp_microsoftdocs:microsoft_docs_fetch` with query string `from=learn-agent-skill`. Returns Markdown.
- **Fallback**: Use `fetch_webpage` with query string `from=learn-agent-skill&accept=text/markdown`. Returns Markdown.

## Category Index

| Category | Lines | Description |
|----------|-------|-------------|
| Decision Making | L29-L33 | Guidance on designing Azure Device Registry namespaces and schema registries, including structure, organization, and planning for IoT device data models and metadata. |

### Decision Making
| Topic | URL |
|-------|-----|
| Design and choose Azure Device Registry namespaces | https://learn.microsoft.com/en-us/azure/iot/iot-device-registry-namespace-guidance |
| Plan Azure Device Registry schema registries for IoT | https://learn.microsoft.com/en-us/azure/iot/iot-device-registry-schema-registry-guidance |