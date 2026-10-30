# Testing Guidance — RTC Web (`agora-rtc-sdk-ng`)

Mock at the module boundary. The key interfaces to mock:

- `AgoraRTC.createClient()` → mock client with `join`, `leave`, `publish`, `subscribe`
- `AgoraRTC.createMicrophoneAudioTrack()` / `createCameraVideoTrack()` → mock tracks
- `client.on(event, handler)` → capture event handlers for test assertions

Pattern: use Jest's `jest.mock` with a manual mock file.

```javascript
// __mocks__/agora-rtc-sdk-ng.js
const mockClient = {
  join: jest.fn().mockResolvedValue(undefined),
  leave: jest.fn().mockResolvedValue(undefined),
  publish: jest.fn().mockResolvedValue(undefined),
  subscribe: jest.fn().mockResolvedValue(undefined),
  renewToken: jest.fn().mockResolvedValue(undefined),
  on: jest.fn(),
  off: jest.fn(),
};

const mockTrack = {
  play: jest.fn(),
  stop: jest.fn(),
  close: jest.fn(),
  setEnabled: jest.fn().mockResolvedValue(undefined),
  getVolumeLevel: jest.fn().mockReturnValue(0.5),
};

const AgoraRTC = {
  createClient: jest.fn().mockReturnValue(mockClient),
  createMicrophoneAudioTrack: jest.fn().mockResolvedValue({ ...mockTrack }),
  createCameraVideoTrack: jest.fn().mockResolvedValue({ ...mockTrack }),
};

module.exports = AgoraRTC;
module.exports.default = AgoraRTC;
```

In tests, call `jest.mock('agora-rtc-sdk-ng')` at the top of the file to activate the
manual mock automatically.

Capture event handlers so tests can simulate SDK callbacks:

```javascript
test('subscribes when user-published fires', async () => {
  const handlers = {}
  mockClient.on.mockImplementation((event, cb) => {
    handlers[event] = cb
  })

  render(<VideoCall />)

  const user = {
    uid: 42,
    audioTrack: { play: jest.fn() },
    videoTrack: { play: jest.fn() },
  }

  const onUserPublished = handlers['user-published']
  await onUserPublished(user, 'audio')

  expect(mockClient.subscribe).toHaveBeenCalledWith(user, 'audio')
  expect(user.audioTrack.play).toHaveBeenCalled()
})
```

Token renewal is a required production behavior:

```javascript
test('renews token before expiry', async () => {
  global.fetch = jest.fn().mockResolvedValue({
    ok: true,
    json: async () => ({ token: 'new-token-xyz' }),
  })

  const handler = mockClient.on.mock.calls
    .find(([e]) => e === 'token-privilege-will-expire')[1]

  await handler()

  expect(fetch).toHaveBeenCalledWith(expect.stringContaining('/token'))
  expect(mockClient.renewToken).toHaveBeenCalledWith('new-token-xyz')
})
```

Primary assertions:

- joins the correct channel/UID
- publishes expected tracks
- subscribes after remote publish events
- renews token before expiry
- stops and closes tracks before leave
