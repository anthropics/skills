# Python MCP Server Template

```python
from fastmcp import FastMCP
import httpx
import os

mcp = FastMCP(name="my-server")
API_BASE = os.environ["API_BASE"]
API_TOKEN = os.environ["API_TOKEN"]

@mcp.tool()
def list_items(input: dict) -> dict:
    with httpx.Client(base_url=API_BASE, headers={"Authorization": f"Bearer {API_TOKEN}"}) as client:
        resp = client.get("/items", params=input)
        if resp.status_code >= 400:
            return {"error": {"code": "upstream_error", "message": "List failed", "details": resp.text}}
        return resp.json()

if __name__ == "__main__":
    mcp.run()
```
