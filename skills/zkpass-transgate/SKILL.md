---
name: zkpass-transgate
description: >
  Integrate the zkPass TransGate JS-SDK into JavaScript/TypeScript web3 DApps to enable
  zero-knowledge proof (ZKP) based private data validation. Use this skill whenever the user
  mentions zkPass, TransGate, transgate-js-sdk, ZKP verification in a DApp, private data validation,
  zkPass schema, appID/schemaId setup, on-chain or off-chain proof verification, or wants to let
  users prove facts about their web2 data (age, credit score, KYC status, etc.) without revealing
  the raw data. Trigger even when the user just says "zkpass integration", "add zkpass to my dapp",
  or "verify user data with zkpass".
---

# zkPass TransGate JS-SDK Integration Skill

This skill guides you through integrating `@zkpass/transgate-js-sdk` into a JavaScript or
TypeScript DApp. zkPass TransGate lets users prove facts about their private HTTPS data
(e.g., age, balance, KYC status) using Zero-Knowledge Proofs without exposing the raw data.

## How It Works (Mental Model)

1. **DApp** creates a `TransgateConnect` instance with its `appId`
2. **User** triggers verification; the DApp calls `connector.launch(schemaId)`
3. **SDK** contacts the allocator node, which validates the schema and returns task info
4. **TransGate** (browser extension or mobile app) opens the target data-source site, performs
   a 3P-TLS session, and generates a ZK proof locally in the browser
5. **Validator node** verifies the proof and returns the result back to the DApp via the SDK
6. **DApp** uses the result for on-chain or off-chain verification

## Prerequisites

Before writing any code, complete these setup steps in the [zkPass DevHub](https://dev.zkpass.org):

1. Connect wallet -> create a project -> copy the **appId**
2. Click **Add Schema** -> configure assertions -> copy the **schemaId**
3. End-users need the **TransGate browser extension** or **TransGate mobile app**

## Installation

```bash
npm install @zkpass/transgate-js-sdk
# or
yarn add @zkpass/transgate-js-sdk
```

> In Next.js/SSR environments, always call the SDK inside a `useEffect` / client-side guard only.

## Core API

| Method | Description |
|--------|-------------|
| `new TransgateConnect(appId)` | Creates connector instance |
| `connector.isTransgateAvailable()` | `Promise<boolean>` - checks if extension is installed |
| `connector.launch(schemaId, address?)` | Starts ZKP verification; optional wallet address binds to proof |

### Result Object Fields
- `taskId`, `uHash`, `publicFields`, `publicFieldsHash`
- `validatorAddress`, `validatorSignature`
- `allocatorAddress`, `allocatorSignature`

## Integration Steps

### Step 1: Import and instantiate
```ts
import TransgateConnect from '@zkpass/transgate-js-sdk'
const connector = new TransgateConnect('YOUR_APP_ID')
```

### Step 2: Check availability
```ts
const isAvailable = await connector.isTransgateAvailable()
if (!isAvailable) {
  alert('Please install the TransGate extension or mobile app.')
  return
}
```

### Step 3: Launch verification
```ts
const result = await connector.launch('YOUR_SCHEMA_ID')
// With wallet address binding (recommended for on-chain use):
const result = await connector.launch('YOUR_SCHEMA_ID', '0xYourAddress')
```

### Step 4: Use the result
```ts
await verifyOffChain(result)  // backend signature check
await submitOnChain(result)   // smart contract call
```

## On-Chain vs Off-Chain Verification

| | On-Chain | Off-Chain |
|---|---|---|
| Use when | Smart contract needs proof (DeFi, NFT, DAO) | Traditional backend, no gas costs |
| How | Call verifier contract with result fields | Check validator/allocator signatures on backend |

## Error Handling
```ts
try {
  const result = await connector.launch(schemaId, address)
} catch (err) {
  if (err.message?.includes('not installed')) showInstallPrompt()
  else if (err.message?.includes('cancel')) showRetryOption()
  else showGenericError()
}
```

## Common Patterns

### Gating content
```ts
const verified = await runZkPassVerification()
if (verified) unlockContent()
```

### Checking public fields
```ts
const result = await connector.launch(schemaId)
console.log(result.publicFields) // e.g. { age_gte_18: true }
```

## Reference Files

- `references/code-examples.md` - React hook, React component, Next.js, vanilla JS,
  off-chain (ethers.js) and on-chain (Solidity) verification examples

## Useful Links

- [zkPass DevHub](https://dev.zkpass.org)
- [zkPass Docs](https://docs.zkpass.org/developer-guides/js-sdk)
- [GitHub: Transgate-JS-SDK](https://github.com/zkPassOfficial/Transgate-JS-SDK)
- [npm: @zkpass/transgate-js-sdk](https://www.npmjs.com/package/@zkpass/transgate-js-sdk)
