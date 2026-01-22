---
name: phantom-connect
description: Build wallet-connected applications with Phantom Connect SDKs for Solana blockchain integration
---

# Phantom Connect Development Skill

A Claude Code skill for building wallet-connected applications with Phantom Connect SDKs.

## Overview

This skill provides Claude with deep knowledge of the Phantom Connect SDK ecosystem:

- **React SDK**: `@phantom/react-sdk` for React web apps
- **React Native SDK**: `@phantom/react-native-sdk` for mobile apps  
- **Browser SDK**: `@phantom/browser-sdk` for vanilla JS/TS
- **Solana**: Full Solana blockchain support
- **Auth Methods**: Social login (Google, Apple), browser extension

## When to Use This Skill

Claude should use this skill when users ask about:

- Phantom wallet integration
- Connecting wallets in React/React Native/vanilla JS apps
- Signing messages or transactions with Phantom
- Token-gated access patterns
- NFT minting with wallet connection
- Crypto payment flows
- Solana wallet support

## SDK Selection

| Platform | SDK | Package |
|----------|-----|---------|
| React web apps | React SDK | `@phantom/react-sdk` |
| React Native / Expo | React Native SDK | `@phantom/react-native-sdk` |
| Vanilla JS / Vue / Angular | Browser SDK | `@phantom/browser-sdk` |

## Prerequisites

All integrations require:

1. **Phantom Portal Account** - Register at [phantom.com/portal](https://phantom.com/portal)
2. **App ID** - Get from Portal → App → Set Up
3. **Allowlisted URLs** - Add domains and redirect URLs in Portal

## Core Concepts

### Auth Providers

| Provider | Description | Requires appId |
|----------|-------------|----------------|
| `"injected"` | Phantom browser extension | No |
| `"google"` | Google OAuth (embedded wallet) | Yes |
| `"apple"` | Apple ID (embedded wallet) | Yes |

### Supported Networks

**Solana**: Mainnet-beta, Devnet, Testnet

## Quick Start Patterns

### React SDK

```tsx
import { PhantomProvider, useModal, usePhantom, darkTheme } from "@phantom/react-sdk";
import { AddressType } from "@phantom/browser-sdk";

function App() {
  return (
    <PhantomProvider
      config={{
        providers: ["google", "apple", "injected"],
        appId: "your-app-id",
        addressTypes: [AddressType.solana],
        authOptions: { redirectUrl: "https://yourapp.com/callback" },
      }}
      theme={darkTheme}
    >
      <YourApp />
    </PhantomProvider>
  );
}
```

### React Native SDK

```tsx
// CRITICAL: Must be first import
import "react-native-get-random-values";
import { PhantomProvider, AddressType, darkTheme } from "@phantom/react-native-sdk";

// Requires app.json: { "expo": { "scheme": "myapp", "plugins": [...] } }
```

### Browser SDK

```ts
import { BrowserSDK, AddressType } from "@phantom/browser-sdk";

const sdk = new BrowserSDK({
  providers: ["google", "apple", "injected"],
  appId: "your-app-id",
  addressTypes: [AddressType.solana],
  autoConnect: true,
});
```

## Specialized Topics

For detailed implementation patterns, Claude should read these files:

- **react-sdk.md** - Complete React SDK reference (hooks, components, theming)
- **react-native-sdk.md** - Mobile setup, Expo config, deep links
- **browser-sdk.md** - Vanilla JS patterns, events, wallet discovery
- **transactions.md** - Solana transaction patterns
- **token-gating.md** - Token-gated access implementation
- **nft-minting.md** - NFT mint page patterns
- **payments.md** - Crypto payment flows

## Common Issues

| Issue | Solution |
|-------|----------|
| "appId required" | Add appId from Phantom Portal when using google/apple |
| Redirect not working | Allowlist redirectUrl in Phantom Portal |
| React Native crashes | Import `react-native-get-random-values` as FIRST import |
| Extension not detected | Use `waitForPhantomExtension()` with timeout |

## Resources

- [Phantom Portal](https://phantom.com/portal) - App registration
- [Phantom Docs](https://docs.phantom.com) - Full documentation
- [SDK Examples](https://github.com/phantom/wallet-sdk/tree/main/examples) - Working demos
- [MCP Server](https://docs.phantom.com/resources/mcp-server) - AI docs access
