"""Regression tests for MCP tool discovery across paginated responses."""

import unittest
from types import SimpleNamespace

from connections import MCPConnection


class Connection(MCPConnection):
    def _create_context(self):
        raise NotImplementedError


class V1Session:
    def __init__(self):
        self.cursors = []

    async def list_tools(self, cursor=None):
        self.cursors.append(cursor)
        if cursor is None:
            return SimpleNamespace(
                tools=[SimpleNamespace(name="first", description="first tool", inputSchema={})],
                nextCursor="page-2",
            )
        return SimpleNamespace(
            tools=[SimpleNamespace(name="second", description="second tool", inputSchema={})],
            nextCursor=None,
        )


class V2Session:
    def __init__(self):
        self.cursors = []

    async def list_tools(self, *, params=None):
        cursor = params.cursor if params else None
        self.cursors.append(cursor)
        if cursor is None:
            return SimpleNamespace(
                tools=[SimpleNamespace(name="first", description="first tool", input_schema={})],
                next_cursor="page-2",
            )
        return SimpleNamespace(
            tools=[SimpleNamespace(name="second", description="second tool", input_schema={})],
            next_cursor=None,
        )


class RepeatingCursorSession:
    async def list_tools(self, cursor=None):
        return SimpleNamespace(tools=[], nextCursor="same-page")


class ToolPaginationTests(unittest.IsolatedAsyncioTestCase):
    async def test_v1_client_collects_all_tool_pages(self):
        connection = Connection()
        connection.session = V1Session()

        tools = await connection.list_tools()

        self.assertEqual([tool["name"] for tool in tools], ["first", "second"])
        self.assertEqual(connection.session.cursors, [None, "page-2"])

    async def test_repeated_cursor_fails_instead_of_looping_forever(self):
        connection = Connection()
        connection.session = RepeatingCursorSession()

        with self.assertRaisesRegex(ValueError, "repeated tools/list cursor"):
            await connection.list_tools()

    async def test_v2_client_collects_all_tool_pages(self):
        connection = Connection()
        connection.session = V2Session()

        tools = await connection.list_tools()

        self.assertEqual([tool["name"] for tool in tools], ["first", "second"])
        self.assertEqual(connection.session.cursors, [None, "page-2"])


if __name__ == "__main__":
    unittest.main()
