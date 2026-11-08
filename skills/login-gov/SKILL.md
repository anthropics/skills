---
name: login-gov
description: Integrate with login.gov as a federal identity provider — OIDC and SAML federation, private_key_jwt client authentication, ACR value selection (auth-only, verified, facial-match, PIV/CAC), sandbox and production setup, token flow implementation, user attribute scopes, and Partner Portal configuration. Use this skill whenever the user mentions login.gov, federal SSO, private_key_jwt, IAL2, ACR values, identity proofing, PIV/CAC authentication, the login.gov Partner Portal, or any error from the login.gov IdP — even if they just say "integrate with login.gov" or "federal identity" without more detail.
---

# login-gov

Federal identity provider integration using login.gov. Covers OIDC (preferred) and SAML, private_key_jwt authentication, assurance level selection, and the full token exchange flow.

## When to use

- Integrating a web or mobile app with login.gov for federal SSO
- Choosing between auth-only, identity-verified, and PIV/CAC assurance levels
- Implementing OIDC authorization code + private_key_jwt flow
- Setting up sandbox vs production environments
- Requesting user attributes (email, phone, SSN, x509/PIV)
- Debugging `invalid_client`, `invalid_request`, or token validation errors

Do NOT use for:
- Non-federal identity providers (Okta, Auth0, Cognito — use their own SDKs)
- SAML SP setup (login.gov supports SAML but OIDC is preferred; ask user to confirm)
- Private-sector applications (login.gov is US federal agencies only)

---

## Endpoints

| Environment | Discovery URL |
|------------|--------------|
| Sandbox | `https://idp.int.identitysandbox.gov/.well-known/openid-configuration` |
| Production | `https://secure.login.gov/.well-known/openid-configuration` |

Key endpoints from discovery:
- Authorization: `https://idp.int.identitysandbox.gov/openid_connect/authorize`
- Token: `https://idp.int.identitysandbox.gov/api/openid_connect/token`
- UserInfo: `https://idp.int.identitysandbox.gov/api/openid_connect/userinfo`
- JWKS: `https://idp.int.identitysandbox.gov/api/openid_connect/certs`

---

## Authentication methods

### Web apps — private_key_jwt (required)

Generate a 2048-bit RSA key pair. Register the **public certificate** in the Partner Portal. Sign client assertions with the **private key** using RS256.

```bash
# Generate key pair
openssl genrsa -out private.pem 2048
openssl req -new -x509 -key private.pem -out public.crt -days 365 \
  -subj "/C=US/ST=DC/L=Washington/O=Agency/CN=myapp.agency.gov"

# View public key for Partner Portal upload
cat public.crt
```

### Native mobile apps — PKCE (RFC 7636)

Generate a `code_verifier` (43–128 URL-safe random chars), hash it:
```
code_challenge = BASE64URL(SHA256(code_verifier))
```
Pass `code_challenge` and `code_challenge_method=S256` in the authorization request.

### Explicitly NOT supported

- `client_secret` / `client_secret_post` / `client_secret_basic`
- Implicit flow (`response_type=token`)

---

## ACR values — choose the right level

| ACR value | Meaning | When to use |
|-----------|---------|-------------|
| `urn:acr.login.gov:auth-only` | Password + optional MFA | Content that needs a federal user account but no identity proof |
| `urn:acr.login.gov:verified` | Identity-verified (IAL2), no facial match | Benefits, grants, regulated services |
| `urn:acr.login.gov:verified-facial-match-required` | IAL2 + facial biometric required | High-value transactions, strict identity requirements |
| `urn:acr.login.gov:verified-facial-match-preferred` | IAL2 + facial preferred | Upgrade path — users without cameras can still proceed |

**AAL (Authentication Assurance Level) modifiers** — combine with ACR:

| AAL value | Meaning |
|-----------|---------|
| `urn:gov:gsa:ac:classes:sp:PasswordProtectedTransport:duo` | Default 2FA |
| `http://idmanagement.gov/ns/assurance/aal/2` | Strict AAL2 (non-remembered device) |
| `http://idmanagement.gov/ns/assurance/aal/2?phishing_resistant=true` | Hardware key / passkey required |
| `http://idmanagement.gov/ns/assurance/aal/2?hspd12=true` | PIV/CAC required |

Pass multiple ACR values space-separated in the `acr_values` parameter.

---

## Step 1 — Authorization request

```
GET https://idp.int.identitysandbox.gov/openid_connect/authorize
  ?acr_values=urn:acr.login.gov:auth-only
  &client_id=YOUR_CLIENT_ID
  &nonce=RANDOM_22_CHAR_MIN
  &prompt=select_account
  &redirect_uri=https://yourapp.agency.gov/auth/callback
  &response_type=code
  &scope=openid+email+profile
  &state=RANDOM_22_CHAR_MIN
```

**Rules:**
- `state` and `nonce` must be ≥ 22 characters — login.gov will reject shorter values
- `prompt=select_account` is required (no other values supported)
- `redirect_uri` must exactly match a registered URI in the Partner Portal
- Store `state` in session; store `nonce` for id_token validation

---

## Step 2 — Handle the callback

```
GET https://yourapp.agency.gov/auth/callback
  ?code=AUTH_CODE
  &state=STATE_FROM_STEP1
```

Verify `state` matches the value you stored. Then exchange the code for tokens.

---

## Step 3 — Token exchange

```http
POST https://idp.int.identitysandbox.gov/api/openid_connect/token
Content-Type: application/x-www-form-urlencoded

client_assertion=SIGNED_JWT
&client_assertion_type=urn:ietf:params:oauth:client-assertion-type:jwt-bearer
&code=AUTH_CODE_FROM_CALLBACK
&grant_type=authorization_code
```

### Build the client_assertion JWT

```python
import jwt, time, uuid
from cryptography.hazmat.primitives.serialization import load_pem_private_key

private_key = load_pem_private_key(open("private.pem", "rb").read(), password=None)

claims = {
    "iss": CLIENT_ID,          # your client_id
    "sub": CLIENT_ID,          # also client_id
    "aud": "https://idp.int.identitysandbox.gov/api/openid_connect/token",
    "jti": str(uuid.uuid4()),  # unique per request
    "exp": int(time.time()) + 300,  # 5 minutes max
}

assertion = jwt.encode(claims, private_key, algorithm="RS256")
```

### Token response

```json
{
  "access_token": "TOKEN",
  "token_type": "Bearer",
  "expires_in": 900,
  "id_token": "SIGNED_JWT"
}
```

### Validate the id_token

1. Fetch login.gov's public keys from the JWKS endpoint
2. Verify signature using RS256 with the matching key (`kid` header)
3. Verify `iss` = login.gov IdP URL
4. Verify `aud` = your `client_id`
5. Verify `nonce` = the nonce you sent in Step 1
6. Verify `exp` is in the future

---

## Step 4 — Fetch user attributes

```http
GET https://idp.int.identitysandbox.gov/api/openid_connect/userinfo
Authorization: Bearer ACCESS_TOKEN
```

Response attributes depend on scopes requested:

| Scope | Attributes returned |
|-------|-------------------|
| `openid` | `sub` (UUID, stable per client) |
| `email` | `email`, `email_verified` |
| `all_emails` | `all_emails` array |
| `phone` | `phone`, `phone_verified` |
| `profile` | `given_name`, `family_name`, `birthdate`, `verified_at` |
| `profile:name` | `given_name`, `family_name` |
| `profile:birthdate` | `birthdate` |
| `address` | `address` object (street, city, state, zip) |
| `social_security_number` | `social_security_number` |
| `x509` | `x509_subject`, `x509_issuer`, `x509_presented` (PIV/CAC) |

> **Note**: `social_security_number` and identity attributes require `urn:acr.login.gov:verified` or higher. Login.gov will reject the request if the ACR level doesn't support the requested scope.

---

## Sandbox setup

1. Register at **https://dashboard.int.identitysandbox.gov**
2. Create an app — get a `client_id`
3. Upload your `public.crt`
4. Set `redirect_uri` values (can be `http://localhost` for dev)
5. Test users: create accounts at `https://idp.int.identitysandbox.gov`
6. For IAL2 testing: the sandbox has a bypass — enter any SSN/address and it will pass

---

## Production deployment checklist

- [ ] Inter-Agency Agreement (IAA) signed with GSA
- [ ] Production app registered in **https://dashboard.login.gov**
- [ ] Production key pair generated (separate from sandbox)
- [ ] Redirect URIs use HTTPS with valid TLS
- [ ] `state` and `nonce` are cryptographically random, stored server-side
- [ ] id_token signature validation implemented
- [ ] `sub` (UUID) used as the stable user identifier — not email (email can change)
- [ ] Logout: redirect to `https://secure.login.gov/openid_connect/logout?client_id=...&post_logout_redirect_uri=...&state=...`

---

## Common errors

| Error | Cause | Fix |
|-------|-------|-----|
| `invalid_client` | Wrong `client_id` or bad JWT signature | Verify `client_id` matches Partner Portal; check key pair matches |
| `invalid_request: nonce too short` | nonce < 22 chars | Generate ≥ 22 char random string |
| `redirect_uri_mismatch` | URI not registered | Add exact URI to Partner Portal (including trailing slash) |
| `invalid_scope` | Scope not allowed for ACR level | Use `urn:acr.login.gov:verified` for identity attributes |
| id_token nonce mismatch | Nonce not stored/retrieved correctly | Store nonce in server-side session before redirect |
| `exp` claim rejected | client_assertion JWT older than 5 min | Always generate assertion fresh per token request |

## Example prompts

- *"How do I integrate our agency web app with login.gov for federal SSO?"*
- *"Generate the `private_key_jwt` client assertion JWT for the token exchange."*
- *"What ACR value do I use if I need identity verification but not facial recognition?"*
- *"My token request returns `invalid_client`. What could cause that?"*
- *"How do I request the user's SSN and address attributes after they authenticate?"*
- *"Walk me through setting up the login.gov sandbox — discovery URL, test users, IAL2 bypass."*
- *"What's the production deployment checklist before we go live with login.gov?"*

## Related skills

- [`arcgis-enterprise-k8s`](./arcgis-enterprise-k8s/SKILL.md) — if fronting ArcGIS with federal identity via login.gov
- [`ubuntu24-stig`](./ubuntu24-stig/SKILL.md) — OS hardening for the server running the integration
