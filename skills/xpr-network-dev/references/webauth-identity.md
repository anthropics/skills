# WebAuth and Identity on XPR Network

This guide covers WebAuth wallet integration, user profiles, and KYC/identity verification.

## WebAuth Overview

WebAuth is XPR Network's native wallet supporting:
- **WebAuthn authentication** - Face ID, fingerprint, security keys
- **Account abstraction** - Human-readable accounts
- **No seed phrases** - Hardware-backed keys
- **Cross-device** - Mobile app and web wallet

### Wallet Options

| Wallet | Type | Use Case |
|--------|------|----------|
| WebAuth Mobile | iOS/Android app | Primary consumer wallet |
| webauth.com | Web wallet | Browser-based, no install |
| Anchor | Desktop app | Power users, developers |

---

## User Profiles

User profiles are stored in the `eosio.proton` contract.

### Profile Table Structure

```typescript
interface UserInfo {
  acc: string;           // Account name
  name: string;          // Display name
  avatar: string;        // Avatar URL or base64
  verified: boolean;     // Blue checkmark
  verifiedon: number;    // Verification timestamp
  date: number;          // Registration date
  fullname: string;      // Full legal name (if KYC)
  kyc: KYCProvider[];    // KYC verifications
}

interface KYCProvider {
  kyc_provider: string;  // Provider account
  kyc_level: string;     // Verification level
  kyc_date: number;      // Verification date
}
```

### Query User Profile

```typescript
async function getUserProfile(account: string) {
  const { rows } = await rpc.get_table_rows({
    code: 'eosio.proton',
    scope: 'eosio.proton',
    table: 'usersinfo',
    lower_bound: account,
    upper_bound: account,
    limit: 1
  });

  return rows[0] ?? null;
}

// Example response
{
  "acc": "alice",
  "name": "Alice",
  "avatar": "https://gateway.pinata.cloud/ipfs/Qm...",
  "verified": true,
  "verifiedon": 1705123456,
  "date": 1704567890,
  "fullname": "",
  "kyc": [
    {
      "kyc_provider": "eosio.proton",
      "kyc_level": "2",
      "kyc_date": 1705123456
    }
  ]
}
```

### Check KYC Status

```typescript
async function isKYCVerified(account: string): Promise<boolean> {
  const profile = await getUserProfile(account);

  if (!profile) return false;

  // Check for any KYC entry
  return profile.kyc && profile.kyc.length > 0;
}

async function getKYCLevel(account: string): Promise<number> {
  const profile = await getUserProfile(account);

  if (!profile || !profile.kyc || profile.kyc.length === 0) {
    return 0;  // Not KYC'd
  }

  // Get highest level
  return Math.max(...profile.kyc.map(k => parseInt(k.kyc_level)));
}
```

### KYC Levels

| Level | Description |
|-------|-------------|
| 0 | Not verified |
| 1 | Basic verification (email) |
| 2 | Identity verified (ID document) |
| 3 | Enhanced verification (additional docs) |

---

## Update User Profile

```typescript
async function updateProfile(
  session: any,
  name: string,
  avatar: string
) {
  return session.transact({
    actions: [{
      account: 'eosio.proton',
      name: 'updateuser',
      authorization: [session.auth],
      data: {
        acc: session.auth.actor,
        name: name,
        avatar: avatar
      }
    }]
  }, { broadcast: true });
}
```

---

## Display User Info

### Avatar Component

```tsx
interface AvatarProps {
  account: string;
  avatar?: string;
  size?: number;
}

export function Avatar({ account, avatar, size = 40 }: AvatarProps) {
  const [src, setSrc] = useState(avatar);
  const [error, setError] = useState(false);

  // Fallback to generated avatar
  const fallback = `https://avatars.dicebear.com/api/identicon/${account}.svg`;

  return (
    <img
      src={error ? fallback : (src || fallback)}
      alt={account}
      width={size}
      height={size}
      style={{ borderRadius: '50%' }}
      onError={() => setError(true)}
    />
  );
}
```

### User Card Component

```tsx
interface UserCardProps {
  account: string;
}

export function UserCard({ account }: UserCardProps) {
  const [profile, setProfile] = useState<UserInfo | null>(null);

  useEffect(() => {
    async function load() {
      const p = await getUserProfile(account);
      setProfile(p);
    }
    load();
  }, [account]);

  const isKYC = profile?.kyc?.length > 0;

  return (
    <div className="user-card">
      <Avatar account={account} avatar={profile?.avatar} size={60} />
      <div>
        <h3>{profile?.name || account}</h3>
        <span className="account">@{account}</span>
        {profile?.verified && <span className="checkmark">✓ Verified</span>}
        {isKYC && <span className="kyc-badge">KYC</span>}
      </div>
    </div>
  );
}
```

---

## WebAuth SDK Integration

### Login Flow

```typescript
import ProtonWebSDK from '@proton/web-sdk';

async function login() {
  const { link, session } = await ProtonWebSDK({
    linkOptions: {
      chainId: '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0',
      endpoints: ['https://proton.eosusa.io'],
      restoreSession: false
    },
    transportOptions: {
      requestAccount: 'myapp'
    },
    selectorOptions: {
      appName: 'My App',
      appLogo: 'https://myapp.com/logo.png',
      enabledWalletTypes: ['proton', 'webauth', 'anchor']
    }
  });

  // Get user profile after login
  const profile = await getUserProfile(session.auth.actor);

  return {
    session,
    profile,
    isKYC: profile?.kyc?.length > 0
  };
}
```

### Require KYC for Actions

```typescript
async function requireKYC(session: any) {
  const profile = await getUserProfile(session.auth.actor);

  if (!profile?.kyc?.length) {
    throw new Error('KYC verification required. Please verify your identity in WebAuth.');
  }

  return true;
}

// Usage
async function performKYCAction(session: any, data: any) {
  await requireKYC(session);

  // Proceed with action
  return session.transact({
    actions: [/* ... */]
  });
}
```

### Deep Link to WebAuth

```typescript
// Redirect to WebAuth for KYC
function redirectToKYC() {
  window.location.href = 'https://webauth.com/verify';
}

// Open specific account in WebAuth
function openInWebAuth(account: string) {
  window.location.href = `https://webauth.com/wallet/${account}`;
}
```

---

## Verification in Contracts

### Check KYC On-Chain

```typescript
import { Name, TableStore, check } from 'proton-tsc';

// Define the usersinfo table structure
@table("usersinfo", noabigen)
class UserInfo extends Table {
  constructor(
    public acc: Name = new Name(),
    public name: string = "",
    public avatar: string = "",
    public verified: boolean = false
    // kyc array handling requires custom deserialization
  ) { super(); }

  @primary
  get primary(): u64 { return this.acc.N; }
}

@action("kycaction")
kycRequiredAction(user: Name): void {
  requireAuth(user);

  // Query eosio.proton usersinfo
  const usersTable = new TableStore<UserInfo>(
    Name.fromString("eosio.proton"),
    Name.fromString("eosio.proton").N
  );

  const userInfo = usersTable.get(user.N);
  check(userInfo != null, "User not found");
  check(userInfo.verified, "User must be verified");

  // Proceed with action...
}
```

---

## Privacy Considerations

### Minimal Data Collection

```typescript
// Only request what you need
const profile = await getUserProfile(account);

// Don't store fullname or KYC details
const publicProfile = {
  account: profile.acc,
  displayName: profile.name,
  avatar: profile.avatar,
  verified: profile.verified
};
```

### User Consent

```tsx
function VerificationRequest() {
  return (
    <div>
      <p>This action requires identity verification.</p>
      <p>We will check your verification status with WebAuth.</p>
      <p>We do not store your personal information.</p>
      <button onClick={checkKYC}>Continue</button>
    </div>
  );
}
```

---

## Quick Reference

### Query User Info

```bash
# Get user profile
proton table eosio.proton usersinfo -l ACCOUNT -u ACCOUNT
```

### Profile Fields

| Field | Description |
|-------|-------------|
| `acc` | Account name |
| `name` | Display name |
| `avatar` | Avatar URL/base64 |
| `verified` | Blue checkmark |
| `kyc` | Array of KYC verifications |

### KYC Check Pattern

```typescript
const profile = await getUserProfile(account);
const isKYC = profile?.kyc?.length > 0;
const kycLevel = Math.max(...(profile?.kyc?.map(k => parseInt(k.kyc_level)) ?? [0]));
```
