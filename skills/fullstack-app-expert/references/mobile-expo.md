# Mobile Development — React Native & Expo (2025-2026)

## The Modern Expo Stack

As of 2025-2026, the recommended React Native stack is:
- **Expo SDK 52-54** (SDK 53 has React 19 + React Native 0.79)
- **Expo Router v4-v5** — file-based routing (Next.js-style)
- **New Architecture** — enabled by default since SDK 52
- **EAS (Expo Application Services)** — build, submit, and update
- **TypeScript** — mandatory for any serious app

---

## New Architecture — What Changed

React Native's New Architecture is enabled by default in Expo SDK 52+ (React Native 0.76+):

- **JSI (JavaScript Interface)**: Direct JS-to-native calls without bridge serialization — synchronous, orders of magnitude faster for native modules
- **Fabric Renderer**: New concurrent rendering engine aligned with React 18/19 concurrent features
- **TurboModules**: Lazy-loaded, type-safe native modules (replaces NativeModules)
- **Bridgeless Mode**: Eliminates the old async message bridge entirely
- **Mitigation for migration**: Most popular libraries have been updated. Check `reactnative.directory` for compatibility.

---

## Expo Router — File-Based Routing

Expo Router v5 (Expo SDK 54) mirrors Next.js App Router concepts for universal apps (iOS, Android, web).

```
app/
  _layout.tsx           # Root layout (navigation container)
  index.tsx             # / route (home)
  (tabs)/               # Route group with shared tab bar layout
    _layout.tsx         # Tab navigator setup
    home.tsx            # /home
    profile.tsx         # /profile
  posts/
    [id].tsx            # /posts/123 (dynamic segment)
    _layout.tsx
  (auth)/               # Route group (no URL segment added)
    login.tsx
    signup.tsx
  +not-found.tsx        # 404 screen
```

```tsx
// app/(tabs)/_layout.tsx:
import { Tabs } from 'expo-router';
import { Ionicons } from '@expo/vector-icons';

export default function TabLayout() {
  return (
    <Tabs screenOptions={{ tabBarActiveTintColor: '#007AFF' }}>
      <Tabs.Screen
        name="home"
        options={{
          title: 'Home',
          tabBarIcon: ({ color }) => <Ionicons name="home" size={24} color={color} />,
        }}
      />
      <Tabs.Screen
        name="profile"
        options={{ title: 'Profile', tabBarIcon: ({ color }) => <Ionicons name="person" size={24} color={color} /> }}
      />
    </Tabs>
  );
}

// Type-safe navigation:
import { Link, useRouter } from 'expo-router';
<Link href="/posts/123">View Post</Link>
const router = useRouter();
router.push('/posts/123');
router.replace('/(tabs)/home');
```

### Expo Router v5 — Type-Safe Routes
```ts
// Enable typed routes in app.json:
{ "expo": { "experiments": { "typedRoutes": true } } }

// Now router.push('/posts/123') is type-checked
// href prop on <Link> autocompletes all routes
```

---

## Streaming AI in React Native (Expo SDK 52+)

Expo SDK 52 introduced `expo/fetch` — a streaming-capable fetch implementation:
```bash
npx expo install expo
```

```tsx
// Use expo/fetch instead of native fetch for streaming:
import { fetch } from 'expo/fetch';
import { useChat } from '@ai-sdk/react';

// useChat hook works in Expo SDK 52+ with expo/fetch:
export default function ChatScreen() {
  const { messages, input, handleInputChange, handleSubmit, isLoading } = useChat({
    api: 'https://api.example.com/chat',
    fetch,  // pass expo/fetch
  });

  return (
    <View>
      <FlatList
        data={messages}
        keyExtractor={(m) => m.id}
        renderItem={({ item }) => (
          <Text>{item.role === 'user' ? 'You: ' : 'AI: '}{item.content}</Text>
        )}
      />
      <TextInput value={input} onChangeText={handleInputChange} />
      <Button title="Send" onPress={handleSubmit} disabled={isLoading} />
    </View>
  );
}
```

Known gotcha: some version combinations of `ai` and `expo` have streaming issues (tracked in vercel/ai#5263). Pin `ai@4.3+` with `expo@52.0.40+`.

---

## EAS — Expo Application Services

### EAS Build
Cloud builds for iOS and Android without needing a Mac.
```bash
npx eas-cli build --platform all --profile production
npx eas-cli build --platform android --profile preview
```

```json
// eas.json:
{
  "build": {
    "development": {
      "developmentClient": true,
      "distribution": "internal"
    },
    "preview": {
      "distribution": "internal",
      "ios": { "simulator": true }
    },
    "production": {
      "autoIncrement": true
    }
  }
}
```

### EAS Submit — App Store Automation
```bash
npx eas-cli submit --platform ios --latest   # submits to TestFlight
npx eas-cli submit --platform android --latest
```

### EAS Update — Over-the-Air Updates
OTA updates change JavaScript and assets without a new App Store submission. Native code changes (new permissions, native modules) still require a full binary build.

```bash
npx eas-cli update --branch production --message "Fix checkout bug"
```

```tsx
// In-app update check:
import * as Updates from 'expo-updates';

async function checkForUpdates() {
  const update = await Updates.checkForUpdateAsync();
  if (update.isAvailable) {
    await Updates.fetchUpdateAsync();
    await Updates.reloadAsync();
  }
}
```

---

## Native Modules (New Architecture)

With Turbo Modules, native modules are synchronous and type-safe:
```ts
// Existing community modules for common needs:
import * as Camera from 'expo-camera';
import * as FileSystem from 'expo-file-system';
import * as Notifications from 'expo-notifications';
import * as SecureStore from 'expo-secure-store';
import * as Haptics from 'expo-haptics';
```

For custom native modules, use **Expo Modules API** (recommended over old NativeModules approach):
```swift
// iOS (Swift):
public class MyModule: Module {
  public func definition() -> ModuleDefinition {
    Name("MyModule")
    Function("getValue") { return "hello from native" }
  }
}
```

---

## React Native Styling Patterns

### NativeWind (Tailwind for React Native)
```bash
npx expo install nativewind tailwindcss
```
```tsx
import { View, Text } from 'react-native';
import { styled } from 'nativewind';

const StyledView = styled(View);
const StyledText = styled(Text);

<StyledView className="flex-1 items-center justify-center bg-white">
  <StyledText className="text-2xl font-bold text-gray-900">Hello</StyledText>
</StyledView>
```

### StyleSheet (Native, Maximum Performance)
```tsx
import { StyleSheet } from 'react-native';
const styles = StyleSheet.create({
  container: { flex: 1, alignItems: 'center', padding: 16 },
  title: { fontSize: 24, fontWeight: 'bold', color: '#111' },
});
```

### Shopify's Restyle / React Native Reusables
Type-safe design system approach. `@shopify/restyle` provides ThemeProvider + typed component variants.

---

## Performance Patterns for React Native

- Use `FlatList` or `FlashList` (Shopify, 10x faster) for long lists — never map arrays to Views
- Use `useCallback` and `memo` for list renderItem — React Compiler handles this automatically
- Avoid inline functions/objects in JSX (causes re-renders)
- Use Hermes engine (default in Expo SDK 49+) for faster JS startup
- Avoid `console.log` in production builds — use babel plugin to strip them
- Use `react-native-mmkv` instead of AsyncStorage for synchronous, fast local storage

---

## Testing React Native Apps

```bash
# Unit/integration: Vitest or Jest + React Native Testing Library:
npx expo install @testing-library/react-native jest

# E2E: Maestro (simple YAML-based) or Detox:
brew install maestro
# maestro test flows/login.yaml
```

```yaml
# flows/login.yaml (Maestro):
appId: com.example.app
---
- launchApp
- tapOn: "Email"
- inputText: "test@example.com"
- tapOn: "Password"
- inputText: "password123"
- tapOn: "Sign In"
- assertVisible: "Welcome"
```
