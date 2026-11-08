# zkPass TransGate — Code Examples

## 1. React Hook (useZkPass.ts)

A reusable React hook that encapsulates the full verification lifecycle.

```tsx
// hooks/useZkPass.ts
import { useState, useCallback } from 'react'
import TransgateConnect from '@zkpass/transgate-js-sdk'

interface ZkPassResult {
  allocatorAddress: string
  allocatorSignature: string
  publicFields: string[]
  publicFieldsHash: string
  taskId: string
  uHash: string
  validatorAddress: string
  validatorSignature: string
}

interface UseZkPassOptions {
  appId: string
  schemaId: string
  walletAddress?: string
}

export function useZkPass({ appId, schemaId, walletAddress }: UseZkPassOptions) {
  const [loading, setLoading] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [result, setResult] = useState<ZkPassResult | null>(null)

  const verify = useCallback(async () => {
    setLoading(true)
    setError(null)
    setResult(null)
    try {
      const connector = new TransgateConnect(appId)
      const isAvailable = await connector.isTransgateAvailable()
      if (!isAvailable) {
        throw new Error('TransGate extension not installed. Please install it from the Chrome Web Store.')
      }
      const res = await connector.launch(schemaId, walletAddress)
      setResult(res as ZkPassResult)
      return res
    } catch (err: any) {
      const message = err?.message ?? 'Verification failed'
      setError(message)
      throw err
    } finally {
      setLoading(false)
    }
  }, [appId, schemaId, walletAddress])

  return { verify, loading, error, result }
}
```

## 2. React Component (VerifyButton.tsx)

```tsx
// components/VerifyButton.tsx
import React from 'react'
import { useZkPass } from '../hooks/useZkPass'

const APP_ID = 'YOUR_APP_ID'
const SCHEMA_ID = 'YOUR_SCHEMA_ID'

interface VerifyButtonProps {
  walletAddress?: string
  onSuccess?: (result: any) => void
  onError?: (error: string) => void
}

export function VerifyButton({ walletAddress, onSuccess, onError }: VerifyButtonProps) {
  const { verify, loading, error, result } = useZkPass({
    appId: APP_ID,
    schemaId: SCHEMA_ID,
    walletAddress,
  })

  const handleVerify = async () => {
    try {
      const res = await verify()
      onSuccess?.(res)
    } catch (err: any) {
      onError?.(err.message)
    }
  }

  return (
    <div>
      <button onClick={handleVerify} disabled={loading}>
        {loading ? 'Verifying...' : 'Verify with zkPass'}
      </button>
      {error && <p style={{ color: 'red' }}>{error.includes('not installed') ? 'Please install the TransGate extension first.' : error}</p>}
      {result && <p style={{ color: 'green' }}>Verification successful! Task ID: {result.taskId}</p>}
    </div>
  )
}
```

## 3. Next.js Client Component

```tsx
// app/verify/page.tsx
'use client'

import { useState } from 'react'
import TransgateConnect from '@zkpass/transgate-js-sdk'

export default function VerifyPage() {
  const [status, setStatus] = useState<'idle' | 'loading' | 'success' | 'error'>('idle')
  const [proof, setProof] = useState<any>(null)

  const handleVerify = async () => {
    setStatus('loading')
    try {
      const connector = new TransgateConnect(process.env.NEXT_PUBLIC_ZKPASS_APP_ID!)
      const isAvailable = await connector.isTransgateAvailable()
      if (!isAvailable) {
        alert('Please install the TransGate browser extension.')
        setStatus('idle')
        return
      }
      const result = await connector.launch(process.env.NEXT_PUBLIC_ZKPASS_SCHEMA_ID!)
      setProof(result)
      setStatus('success')
      await fetch('/api/verify-proof', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(result),
      })
    } catch (err) {
      console.error(err)
      setStatus('error')
    }
  }

  return (
    <main>
      <h1>Verify Your Identity</h1>
      <button onClick={handleVerify} disabled={status === 'loading'}>
        {status === 'loading' ? 'Verifying...' : 'Start Verification'}
      </button>
      {status === 'success' && <p>Verified!</p>}
      {status === 'error' && <p>Verification failed. Please try again.</p>}
    </main>
  )
}
```

```
# .env.local
NEXT_PUBLIC_ZKPASS_APP_ID=your_app_id_here
NEXT_PUBLIC_ZKPASS_SCHEMA_ID=your_schema_id_here
```

## 4. Vanilla JavaScript

```html
<!DOCTYPE html>
<html>
<body>
  <button id="verify-btn">Verify with zkPass</button>
  <p id="status"></p>
  <script type="module">
    import TransgateConnect from 'https://cdn.jsdelivr.net/npm/@zkpass/transgate-js-sdk/+esm'
    const APP_ID = 'YOUR_APP_ID'
    const SCHEMA_ID = 'YOUR_SCHEMA_ID'
    document.getElementById('verify-btn').addEventListener('click', async () => {
      const status = document.getElementById('status')
      status.textContent = 'Verifying...'
      try {
        const connector = new TransgateConnect(APP_ID)
        const available = await connector.isTransgateAvailable()
        if (!available) { status.textContent = 'Please install the TransGate extension.'; return }
        const result = await connector.launch(SCHEMA_ID)
        status.textContent = 'Success! Task: ' + result.taskId
      } catch (err) {
        status.textContent = 'Error: ' + err.message
      }
    })
  </script>
</body>
</html>
```

## 5. Off-Chain Verification (Node.js / Express)

```ts
import { ethers } from 'ethers'

interface ProofResult {
  taskId: string
  schemaId: string
  uHash: string
  publicFieldsHash: string
  validatorAddress: string
  validatorSignature: string
  allocatorAddress: string
  allocatorSignature: string
}

export async function verifyProofOffChain(proof: ProofResult): Promise<boolean> {
  const { taskId, schemaId, uHash, publicFieldsHash, validatorAddress, validatorSignature, allocatorAddress, allocatorSignature } = proof

  // Verify validator signature
  const validatorMessage = ethers.solidityPackedKeccak256(
    ['bytes32', 'bytes32', 'bytes32', 'bytes32'],
    [taskId, schemaId, uHash, publicFieldsHash]
  )
  const recoveredValidator = ethers.recoverAddress(validatorMessage, validatorSignature)
  if (recoveredValidator.toLowerCase() !== validatorAddress.toLowerCase()) throw new Error('Validator signature mismatch')

  // Verify allocator signature
  const allocatorMessage = ethers.solidityPackedKeccak256(
    ['bytes32', 'bytes32', 'address'],
    [taskId, schemaId, validatorAddress]
  )
  const recoveredAllocator = ethers.recoverAddress(allocatorMessage, allocatorSignature)
  if (recoveredAllocator.toLowerCase() !== allocatorAddress.toLowerCase()) throw new Error('Allocator signature mismatch')

  return true
}
```

## 6. On-Chain Verification (Solidity)

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IZkPassVerifier {
    function verifyProof(
        bytes32 taskId, bytes32 schemaId, bytes32 uHash, bytes32 publicFieldsHash,
        address validatorAddress, bytes calldata validatorSignature,
        address allocatorAddress, bytes calldata allocatorSignature
    ) external view returns (bool);
}

contract MyDApp {
    IZkPassVerifier public verifier;
    constructor(address _verifier) { verifier = IZkPassVerifier(_verifier); }

    function onVerified(
        bytes32 taskId, bytes32 schemaId, bytes32 uHash, bytes32 publicFieldsHash,
        address validatorAddress, bytes calldata validatorSignature,
        address allocatorAddress, bytes calldata allocatorSignature
    ) external {
        bool valid = verifier.verifyProof(taskId, schemaId, uHash, publicFieldsHash, validatorAddress, validatorSignature, allocatorAddress, allocatorSignature);
        require(valid, 'Invalid zkPass proof');
        // User is verified — proceed with DApp logic
    }
}
```

> Get the deployed verifier address from the [zkPass DevHub](https://dev.zkpass.org).
