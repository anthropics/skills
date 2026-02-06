# @proton/web-sdk Frontend Integration

This guide covers wallet connection and transaction signing for web applications using `@proton/web-sdk`.

## Installation

```bash
npm install @proton/web-sdk @proton/link
# or
yarn add @proton/web-sdk @proton/link
```

**Important:** The `@proton/link` package is required for mobile wallet support. See [Mobile Wallet Support](#mobile-wallet-support) for details.

## Quick Start

```typescript
import ProtonWebSDK from '@proton/web-sdk';
import '@proton/link'; // Required for mobile wallet support

// Login
const { link, session } = await ProtonWebSDK({
  linkOptions: {
    chainId: '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0',
    endpoints: ['https://proton.eosusa.io']
  },
  selectorOptions: { appName: 'My dApp' }
});

// session.auth = { actor: 'username', permission: 'active' }
console.log('Logged in as:', session.auth.actor);

// Send transaction
const result = await session.transact({
  actions: [{
    account: 'eosio.token',
    name: 'transfer',
    authorization: [session.auth],
    data: {
      from: session.auth.actor,
      to: 'recipient',
      quantity: '1.0000 XPR',
      memo: 'Hello!'
    }
  }]
}, { broadcast: true });
```

---

## ProtonWebSDK Options

### linkOptions (required)

| Key | Type | Required | Description |
|-----|------|----------|-------------|
| `endpoints` | `string[]` | Yes | Array of RPC endpoints (multiple for fault tolerance) |
| `chainId` | `string` | No | Chain ID (defaults to mainnet) |
| `storage` | `LinkStorage` | No | Custom storage adapter |
| `storagePrefix` | `string` | No | Prefix for storage keys (default: `proton-storage`) |
| `restoreSession` | `boolean` | No | Restore previous session without wallet selector |

### transportOptions (optional)

| Key | Type | Description |
|-----|------|-------------|
| `requestAccount` | `string` | Account name requesting transaction (shown in wallet) |
| `backButton` | `boolean` | Show back button in modal (default: true) |

### selectorOptions (optional)

| Key | Type | Description |
|-----|------|-------------|
| `appName` | `string` | Your app name (shown in wallet selector) |
| `appLogo` | `string` | URL to your app logo |
| `enabledWalletTypes` | `string[]` | Wallet types to show: `proton`, `webauth`, `anchor` |
| `customStyleOptions` | `object` | Custom styling for modal |

---

## Complete Service Class Example

```typescript
import ProtonWebSDK from '@proton/web-sdk';

const CHAIN_ID = '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0';
const ENDPOINTS = ['https://proton.eosusa.io', 'https://proton.greymass.com'];

class ProtonService {
  private link: any = null;
  private session: any = null;

  get isLoggedIn(): boolean {
    return this.session !== null;
  }

  get actor(): string {
    return this.session?.auth?.actor ?? '';
  }

  get permission(): string {
    return this.session?.auth?.permission ?? 'active';
  }

  async login(): Promise<{ actor: string; permission: string } | null> {
    try {
      const { link, session } = await ProtonWebSDK({
        linkOptions: {
          chainId: CHAIN_ID,
          endpoints: ENDPOINTS
        },
        transportOptions: {
          requestAccount: 'myapp'
        },
        selectorOptions: {
          appName: 'My dApp',
          appLogo: 'https://myapp.com/logo.png',
          enabledWalletTypes: ['proton', 'webauth', 'anchor']
        }
      });

      this.link = link;
      this.session = session;

      return session.auth;
    } catch (error) {
      console.error('Login failed:', error);
      return null;
    }
  }

  async restoreSession(): Promise<boolean> {
    try {
      const { link, session } = await ProtonWebSDK({
        linkOptions: {
          chainId: CHAIN_ID,
          endpoints: ENDPOINTS,
          restoreSession: true
        },
        transportOptions: {
          requestAccount: 'myapp'
        },
        selectorOptions: {
          appName: 'My dApp'
        }
      });

      if (session) {
        this.link = link;
        this.session = session;
        return true;
      }
      return false;
    } catch (error) {
      console.error('Session restore failed:', error);
      return false;
    }
  }

  async logout(): Promise<void> {
    if (this.link && this.session) {
      await this.link.removeSession('myapp', this.session.auth);
    }
    this.link = null;
    this.session = null;
  }

  async transact(actions: any[]): Promise<any> {
    if (!this.session) {
      throw new Error('Not logged in');
    }

    return this.session.transact(
      { actions },
      { broadcast: true }
    );
  }
}

export const protonService = new ProtonService();
```

---

## Common Actions

### Token Transfer

```typescript
async function transferTokens(to: string, amount: string, memo: string = '') {
  const result = await session.transact({
    actions: [{
      account: 'eosio.token',
      name: 'transfer',
      authorization: [session.auth],
      data: {
        from: session.auth.actor,
        to: to,
        quantity: amount,  // e.g., '10.0000 XPR'
        memo: memo
      }
    }]
  }, { broadcast: true });

  return result;
}
```

### Token Contracts

| Token | Contract | Decimals | Example |
|-------|----------|----------|---------|
| XPR | `eosio.token` | 4 | `1.0000 XPR` |
| XUSDT | `xtokens` | 6 | `1.000000 XUSDT` |
| FOOBAR | `xtokens` | 6 | `1.000000 FOOBAR` |
| LOAN | `loan.token` | 4 | `1.0000 LOAN` |

### Custom Contract Action

```typescript
async function createBattle(amount: string, direction: number, duration: number) {
  const result = await session.transact({
    actions: [{
      account: 'pricebattle',
      name: 'create',
      authorization: [session.auth],
      data: {
        creator: session.auth.actor,
        amount: amount,
        direction: direction,  // 1=UP, 2=DOWN
        oracle_index: 4,       // BTC/USD
        duration: duration     // seconds
      }
    }]
  }, { broadcast: true });

  return result;
}
```

### Multiple Actions in One Transaction

```typescript
async function depositAndStake(amount: string) {
  const result = await session.transact({
    actions: [
      // First action: transfer
      {
        account: 'eosio.token',
        name: 'transfer',
        authorization: [session.auth],
        data: {
          from: session.auth.actor,
          to: 'stakingcontract',
          quantity: amount,
          memo: 'deposit'
        }
      },
      // Second action: stake
      {
        account: 'stakingcontract',
        name: 'stake',
        authorization: [session.auth],
        data: {
          account: session.auth.actor,
          amount: amount
        }
      }
    ]
  }, { broadcast: true });

  return result;
}
```

---

## Custom Styling

```typescript
const { link, session } = await ProtonWebSDK({
  linkOptions: { /* ... */ },
  selectorOptions: {
    appName: 'My dApp',
    customStyleOptions: {
      modalBackgroundColor: '#1a1a2e',
      logoBackgroundColor: '#16213e',
      isLogoRound: true,
      optionBackgroundColor: '#0f3460',
      optionFontColor: '#e94560',
      primaryFontColor: '#ffffff',
      secondaryFontColor: '#a0a0a0',
      linkColor: '#e94560'
    }
  }
});
```

---

## Custom Storage

By default, the SDK uses localStorage. For custom storage (e.g., encrypted storage, server-side):

```typescript
interface LinkStorage {
  write(key: string, data: string): Promise<void>;
  read(key: string): Promise<string | null>;
  remove(key: string): Promise<void>;
}

class SecureStorage implements LinkStorage {
  async write(key: string, data: string): Promise<void> {
    // Your secure storage logic
    localStorage.setItem(key, encrypt(data));
  }

  async read(key: string): Promise<string | null> {
    const data = localStorage.getItem(key);
    return data ? decrypt(data) : null;
  }

  async remove(key: string): Promise<void> {
    localStorage.removeItem(key);
  }
}

const { link, session } = await ProtonWebSDK({
  linkOptions: {
    endpoints: ENDPOINTS,
    storage: new SecureStorage()
  },
  // ...
});
```

---

## React Integration

### Context Provider

```tsx
import React, { createContext, useContext, useState, useEffect } from 'react';
import ProtonWebSDK from '@proton/web-sdk';

interface ProtonContextType {
  session: any;
  login: () => Promise<void>;
  logout: () => Promise<void>;
  transact: (actions: any[]) => Promise<any>;
}

const ProtonContext = createContext<ProtonContextType | null>(null);

export function ProtonProvider({ children }: { children: React.ReactNode }) {
  const [link, setLink] = useState<any>(null);
  const [session, setSession] = useState<any>(null);

  useEffect(() => {
    // Restore session on mount
    restoreSession();
  }, []);

  async function restoreSession() {
    try {
      const { link, session } = await ProtonWebSDK({
        linkOptions: {
          chainId: CHAIN_ID,
          endpoints: ENDPOINTS,
          restoreSession: true
        },
        selectorOptions: { appName: 'My dApp' }
      });

      if (session) {
        setLink(link);
        setSession(session);
      }
    } catch (e) {
      console.error('Restore failed:', e);
    }
  }

  async function login() {
    const { link, session } = await ProtonWebSDK({
      linkOptions: {
        chainId: CHAIN_ID,
        endpoints: ENDPOINTS
      },
      selectorOptions: { appName: 'My dApp' }
    });

    setLink(link);
    setSession(session);
  }

  async function logout() {
    if (link && session) {
      await link.removeSession('myapp', session.auth);
    }
    setLink(null);
    setSession(null);
  }

  async function transact(actions: any[]) {
    if (!session) throw new Error('Not logged in');
    return session.transact({ actions }, { broadcast: true });
  }

  return (
    <ProtonContext.Provider value={{ session, login, logout, transact }}>
      {children}
    </ProtonContext.Provider>
  );
}

export function useProton() {
  const context = useContext(ProtonContext);
  if (!context) throw new Error('useProton must be used within ProtonProvider');
  return context;
}
```

### Usage in Components

```tsx
function WalletButton() {
  const { session, login, logout } = useProton();

  if (session) {
    return (
      <div>
        <span>Connected: {session.auth.actor}</span>
        <button onClick={logout}>Disconnect</button>
      </div>
    );
  }

  return <button onClick={login}>Connect Wallet</button>;
}
```

---

## Error Handling

```typescript
async function safeTransact(actions: any[]) {
  try {
    const result = await session.transact({ actions }, { broadcast: true });
    return { success: true, result };
  } catch (error: any) {
    // User cancelled
    if (error.message?.includes('User cancelled')) {
      return { success: false, error: 'Transaction cancelled by user' };
    }

    // Insufficient resources
    if (error.message?.includes('insufficient')) {
      return { success: false, error: 'Insufficient resources (RAM/CPU/NET)' };
    }

    // Contract assertion failed
    if (error.message?.includes('assertion failure')) {
      const match = error.message.match(/assertion failure with message: (.+)/);
      return { success: false, error: match?.[1] ?? 'Transaction failed' };
    }

    return { success: false, error: error.message ?? 'Unknown error' };
  }
}
```

---

## Mobile Wallet Support

For mobile wallet signing to work (WebAuth iOS/Android app), you **must** install and import `@proton/link`.

### Why @proton/link is Required

The `@proton/link` package provides the transport layer for mobile deep linking. Without it, the SDK cannot communicate with the WebAuth mobile app to request transaction signatures.

### Installation

```bash
npm install @proton/web-sdk @proton/link
```

### Import Pattern

```typescript
import ProtonWebSDK from '@proton/web-sdk';
import '@proton/link'; // Required - enables mobile deep linking transport
```

**Note**: The `@proton/link` import doesn't expose any API you need to call directly. Simply importing it registers the transport handlers needed for mobile wallet communication.

### Dynamic Import Pattern (SSR/Next.js)

For server-side rendering frameworks:

```typescript
if (typeof window !== 'undefined') {
  const sdkReady = Promise.all([
    import('@proton/web-sdk').then((mod) => {
      ProtonWebSDK = mod.default;
    }),
    import('@proton/link')  // Critical for mobile
  ]).then(() => {});
}
```

### Symptoms of Missing @proton/link

If you forget to install/import `@proton/link`:
- Desktop signing works normally
- Mobile browser shows "processing" indefinitely
- WebAuth mobile app never opens for authorization
- May show "unknown requestor" error

### Safari iOS Popup Blocker

Safari iOS blocks popups by default, which prevents the WebAuth browser wallet from opening. Users on Safari iOS should either:

1. Disable popup blocker: **Settings** > **Safari** > **Block Pop-ups** OFF
2. Use the WebAuth mobile app instead of the browser wallet (recommended)
3. Use a different browser (Chrome, Firefox)

**Developer tip**: Show a help message after several seconds of "processing" to guide users to check their popup blocker settings or switch to the WebAuth mobile app.

### Recommended Versions

- `@proton/web-sdk@^4.4.1` or later
- `@proton/link@^3.2.3-27` or later

---

## Known Issues

### WebAuth iOS App Session Caching

**Status**: Unresolved - issue is in WebAuth iOS app

**Symptom**: After logout + login with different account via WebAuth iOS, the UI shows new account but transactions fail with wrong signature.

**Workaround**:
- Force quit WebAuth iOS app before switching accounts
- Or use webauth.com web wallet (works correctly)

### Session Not Restoring

If `restoreSession: true` doesn't restore the session:
- Clear localStorage keys starting with `proton-storage` or your custom prefix
- Ensure you're on the same domain where the session was created
- Check if storage is being blocked (private browsing, etc.)

---

## Next.js Considerations

For SSR frameworks, the SDK must only run client-side:

```typescript
// Only import client-side
let ProtonWebSDK: any;
if (typeof window !== 'undefined') {
  ProtonWebSDK = require('@proton/web-sdk').default;
}

// Check before using
async function login() {
  if (!ProtonWebSDK) {
    console.error('ProtonWebSDK not available');
    return;
  }
  // ...
}
```

Or use dynamic imports:

```typescript
async function login() {
  const { default: ProtonWebSDK } = await import('@proton/web-sdk');
  // ...
}
```

---

## Wallet Types

| Type | Description | Use Case |
|------|-------------|----------|
| `proton` | WebAuth mobile app | Primary mobile wallet |
| `webauth` | webauth.com browser wallet | Web-based, no app needed |
| `anchor` | Anchor desktop wallet | Desktop users, power users |

```typescript
// Show only specific wallets
selectorOptions: {
  enabledWalletTypes: ['proton', 'webauth']  // Hide Anchor
}
```
