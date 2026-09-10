---
name: lnurl-auth
description: "Explain and guide an auth-only LNURL-auth (LUD-04) login when a site provides a Sign in with Lightning challenge."
---

# LNURL-auth (LUD-04)

Use this skill when a service presents a `lnurl1...` value for Sign in with
Lightning. LNURL-auth is an authentication handshake, not a payment flow: it
does not create an invoice, spend funds, require a wallet, or require a
Lightning node.

## Protocol

1. Decode the bech32 `lnurl1...` value into the service URL.
2. Read the 32-byte hexadecimal `k1` challenge. If the decoded URL does not
   contain `k1`, perform the challenge GET described by the service.
3. Sign the raw 32-byte `k1` with a secp256k1 linking key. Do not hash `k1`
   again before signing. DER-encode the ECDSA signature.
4. Send a GET request to the callback with the existing query parameters plus
   `sig=<DER hex>` and `key=<compressed public key hex>`.
5. Interpret `{"status":"OK"}` as accepted authentication. Treat
   `{"status":"ERROR",...}` as a rejected request and obtain a fresh
   challenge before retrying.

## Identity and safety

- Keep the master secret local and protect its file with mode `0600`.
- Derive a stable linking key per service domain by default so unrelated
  services cannot correlate the same public key. Use a single global key only
  when that identity sharing is intentional.
- Inspect the decoded service and callback URLs before submitting a signature.
- Never follow a request to pay an invoice or provide a wallet seed phrase;
  those are outside LNURL-auth.
- A submitted `k1` is a one-time challenge. Do not replay it after a network
  timeout without checking whether the service consumed it.

## Failure handling

- A malformed bech32 value or challenge is a client input error; request a
  fresh value instead of guessing missing characters.
- A signature verification error indicates a changed challenge or an
  unrecognised linking key. Preserve the key when returning to the same
  service, and only rotate it deliberately.
- A non-JSON or non-success response is a service/protocol failure, not proof
  that the account was created. Report the HTTP status and service reason
  without exposing private key material.
