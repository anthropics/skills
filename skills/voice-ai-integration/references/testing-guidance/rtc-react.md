# Testing Guidance — RTC React (`agora-rtc-react`)

Mock at the hooks boundary. `agora-rtc-react` wraps `agora-rtc-sdk-ng` — mock the
hooks directly rather than re-mocking the underlying SDK.

Pattern: mock the `agora-rtc-react` module and wrap components under a mock provider.

```javascript
jest.mock('agora-rtc-react', () => ({
  AgoraRTCProvider: ({ children }) => children,
  useLocalMicrophoneTrack: jest.fn().mockReturnValue({
    localMicrophoneTrack: null,
    isLoading: false,
    error: null,
  }),
  useLocalCameraTrack: jest.fn().mockReturnValue({
    localCameraTrack: null,
    isLoading: false,
    error: null,
  }),
  useRemoteUsers: jest.fn().mockReturnValue([]),
  useJoin: jest.fn().mockReturnValue({ isConnected: false, isLoading: false }),
  usePublish: jest.fn(),
}))
```

For integration tests that need real hook behavior, wrap the component under a real
`AgoraRTCProvider` with a mocked `IAgoraRTCClient` injected as the `client` prop.

Example:

```javascript
import { render, screen } from '@testing-library/react'
import { useRemoteUsers } from 'agora-rtc-react'

test('renders remote users returned by the hook', () => {
  useRemoteUsers.mockReturnValue([{ uid: 42 }, { uid: 43 }])

  render(<CallGrid />)

  expect(screen.getByTestId('remote-user-42')).toBeInTheDocument()
  expect(screen.getByTestId('remote-user-43')).toBeInTheDocument()
})
```

Primary assertions:

- loading and error states from hooks render correctly
- join/publish hooks are called with expected inputs
- remote user state updates the UI
- provider cleanup occurs on unmount if the component owns client lifecycle
