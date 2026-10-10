# SimpleFIN Bridge setup

1. Go to [https://beta-bridge.simplefin.org](https://beta-bridge.simplefin.org) and create an account. Cost: ~$15/year.
2. In the SimpleFIN dashboard, click "Connect" to link each bank. This uses the bank's OAuth flow; SimpleFIN stores read-only credentials.
3. Wait for banks to sync (a few minutes to an hour).
4. Click "Manage" → "New Setup Token" to generate a **base64 setup token**. This token is single-use and short-lived.
5. Claim the token immediately with:
   ```
   python scripts/claim_token.py <base64-token-here>
   ```
   This writes the permanent `SIMPLEFIN_ACCESS_URL` into `.env` without printing the raw secret.
6. If you need to inspect the value before storing it elsewhere, re-run with:
   ```
   python scripts/claim_token.py <base64-token-here> --show-secret
   ```

**Note:** the access URL contains HTTP Basic auth credentials. Treat it as a secret. `ledger-one` validates that it points to a `simplefin.org` host, parses the credentials out before making requests, and never logs the raw URL.
