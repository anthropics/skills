# Joining a Multisig

It is recommended to always create a fresh address on a hardware wallet for each new multisig.

## Verifying address ownership

Creating a proof of address ownership provides important documentation and security assurances to the protocol for all multisig signers. Entity affiliations are acceptable - the goal is accountability, not doxxing.

### Preparing and sharing address & Signature

Sign the message like [@social_handle | name | entity] is looking to join [Multisig Name] X DAO multisig with address 0x... with the private key you intend to use as a signer. One of the options is going using MyCrypto web UI:
1. Connect your wallet to https://app.mycrypto.com/sign-message
2. Enter the message, click "sign" and sign the message on the wallet.
3. The sig field in the result json is the signature hash.

Share the message:
- **Option 1** - Publish the message along with the signature hash on twitter or other easily accessible social media.
- **Option 2** - Share the message privately with multisig admin so it can be stored with multisig documentation

## Ethereum signature verification

### Etherscan UI
1. Go to https://etherscan.io/verifiedSignatures.
2. Click the Verify Signature button.
3. Input address, message & signature hash data & click Continue.
4. See whether the signature provided is valid.
5. To publish: choose "Verify & publish" and click "Continue".
6. After the signature is verified, you'll get the link for sharing.

Note: Enter plain text message (not the hex version MyEtherWallet will give!) and ensure the signature includes the 0x prefix.

### MyCrypto
1. Go to https://app.mycrypto.com/verify-message
2. Enter json & click Verify:

```json
{
 "address": "0x...",
 "msg": "0x...",
 "sig": "signature_hash"
}
```

Note that "msg" is hex text starting with 0x (add 0x before the hex encoded string if necessary). 4. See whether the signature provided is valid.

