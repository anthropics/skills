"""Regression tests for MCP results passed to the evaluation agent."""

import json
import unittest

from mcp.types import CallToolResult, TextContent

from connections import MCPConnection


class Connection(MCPConnection):
    def _create_context(self):
        raise NotImplementedError


class Session:
    def __init__(self, result):
        self.result = result

    async def call_tool(self, name, arguments):
        return self.result


class ToolResultTests(unittest.IsolatedAsyncioTestCase):
    async def test_successful_result_is_json_serializable(self):
        connection = Connection()
        connection.session = Session(CallToolResult(
            content=[TextContent(type="text", text="42")],
            structuredContent={"answer": 42},
            isError=False,
        ))

        result = await connection.call_tool("answer", {})
        encoded = json.dumps(result)

        self.assertEqual(json.loads(encoded)["content"][0]["text"], "42")
        self.assertEqual(result["structuredContent"], {"answer": 42})

    async def test_server_error_status_is_preserved(self):
        connection = Connection()
        connection.session = Session(CallToolResult(
            content=[TextContent(type="text", text="permission denied")],
            isError=True,
        ))

        result = await connection.call_tool("restricted", {})

        self.assertTrue(result["isError"])


if __name__ == "__main__":
    unittest.main()
