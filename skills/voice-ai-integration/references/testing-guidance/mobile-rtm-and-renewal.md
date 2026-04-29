# Testing Guidance — React Native, Flutter, RTM, and Token Renewal

## RTC React Native (`react-native-agora`)

Mock at the module boundary using `jest.mock`. The engine is created via `createAgoraRtcEngine()` — mock the factory and capture the registered event handler so tests can fire callbacks.

```javascript
// __mocks__/react-native-agora.js
const mockEngine = {
  initialize: jest.fn().mockResolvedValue(undefined),
  enableVideo: jest.fn().mockResolvedValue(undefined),
  startPreview: jest.fn().mockResolvedValue(undefined),
  joinChannel: jest.fn().mockResolvedValue(undefined),
  leaveChannel: jest.fn().mockResolvedValue(undefined),
  registerEventHandler: jest.fn(),
  unregisterEventHandler: jest.fn(),
  release: jest.fn().mockResolvedValue(undefined),
}

module.exports = {
  createAgoraRtcEngine: jest.fn().mockReturnValue(mockEngine),
  ChannelProfileType: { ChannelProfileCommunication: 1 },
  ClientRoleType: { ClientRoleBroadcaster: 1, ClientRoleAudience: 2 },
  RtcSurfaceView: 'RtcSurfaceView',
}
```

Simulate callbacks by capturing the registered handler and calling methods directly.

## RTC Flutter (`agora_rtc_engine`)

Use the `mockito` package with `build_runner` to generate mocks. Inject the engine via constructor rather than calling `createAgoraRtcEngine()` directly.

```yaml
dev_dependencies:
  mockito: ^5.4.0
  build_runner: ^2.4.0
```

```dart
@GenerateMocks([RtcEngine])
void main() {}
```

Test join and leave behavior by stubbing async engine methods and verifying the correct parameters.

## RTM Web (`agora-rtm`)

Mock at the module boundary. The `RTM` constructor can throw — the mock should reflect that. Capture `addEventListener` calls so tests can simulate incoming events.

```javascript
const mockRtmClient = {
  login: jest.fn().mockResolvedValue({}),
  logout: jest.fn().mockResolvedValue({}),
  subscribe: jest.fn().mockResolvedValue({}),
  unsubscribe: jest.fn().mockResolvedValue({}),
  publish: jest.fn().mockResolvedValue({}),
  addEventListener: jest.fn(),
}
```

Primary assertions:

- `login` resolves before `subscribe`
- incoming `message` events update UI/state
- presence handling only works when subscribed with `withPresence: true`

## RTM iOS / Android

Use the same native pattern as RTC:

- iOS: protocol-based injection around the RTM client
- Android: interface extraction with Mockito

Capture async completion callbacks so tests can simulate success/failure for login,
subscribe, unsubscribe, and publish.

Primary assertions:

- login happens before subscribe
- publish sends to the correct channel/topic
- message callbacks update state correctly

## Token Renewal Across Platforms

Token renewal is a required production behavior. Cover both RTC and RTM paths:

- RTC Web: `token-privilege-will-expire`
- RTC iOS: `onTokenPrivilegeWillExpire`
- RTC Android: `onTokenPrivilegeWillExpire`
- RTM Web / native: token-expiry or status callbacks for RTM re-login

Web example:

```javascript
test('handles RTM token expiry', async () => {
  global.fetch = jest.fn().mockResolvedValue({
    ok: true,
    json: async () => ({ rtmToken: 'new-rtm-token' }),
  })

  const statusHandler = rtmClient.addEventListener.mock.calls
    .find(([e]) => e === 'status')[1]

  await statusHandler({ state: 'TOKEN_EXPIRED', reason: 'token expired' })

  expect(rtmClient.login).toHaveBeenCalledWith({ token: 'new-rtm-token' })
})
```
