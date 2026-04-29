# Testing Guidance — ConvoAI REST API

Mock at the HTTP client layer. ConvoAI integration generates REST calls — mock the
HTTP client, not the Agora SDK.

## Python

Use `unittest.mock.patch`:

```python
from unittest.mock import patch, MagicMock

@patch('requests.post')
def test_create_agent(mock_post):
    mock_post.return_value = MagicMock(
        status_code=200,
        json=lambda: {"agent_id": "agent_abc123", "status": "STARTING"}
    )

    from your_module import create_agent
    result = create_agent(channel="test-channel", uid="42")

    assert result["agent_id"] == "agent_abc123"
    mock_post.assert_called_once()
    call_kwargs = mock_post.call_args
    assert "Authorization" in call_kwargs.kwargs.get("headers", {})
```

## JavaScript / TypeScript

Use `jest.spyOn` on `global.fetch`:

```javascript
beforeEach(() => {
  jest.spyOn(global, 'fetch').mockResolvedValue({
    ok: true,
    json: async () => ({ agent_id: 'agent_abc123', status: 'STARTING' }),
  })
})

afterEach(() => jest.restoreAllMocks())

test('createAgent sends correct request', async () => {
  await createAgent({ channel: 'test-channel', uid: '42' })
  expect(fetch).toHaveBeenCalledWith(
    expect.stringContaining('/join'),
    expect.objectContaining({ method: 'POST' }),
  )
})
```

If using `axios`, use `axios-mock-adapter` or `jest.spyOn(axios, 'post')`.

## Required Assertions

Every ConvoAI REST integration test should verify:

- `Authorization` header is present
- the request body uses `agent_rtc_uid` as a string, not an integer
- `remote_rtc_uids` is an array of strings
- `name` is unique or generated dynamically
- auth credentials/tokens come from environment or server config, not hardcoded literals
- `/update` sends the full `params` object rather than only the changed field

Example payload assertions:

```javascript
expect(fetch).toHaveBeenCalledWith(
  expect.any(String),
  expect.objectContaining({
    headers: expect.objectContaining({
      Authorization: expect.stringContaining('agora token='),
    }),
    body: expect.stringContaining('"agent_rtc_uid":"0"'),
  }),
)
```

Failure-path tests to include:

- non-200 response surfaces `detail` / `reason`
- 409 agent-name collision retries with a new name
- request failure does not continue with partial local state
