# Registration & Documentation

Proper documentation is essential for multisig security and accountability. This page covers the registration process and required documentation.

## Protocol Documentation

Fill out the registration template and send as a PDF to protocol security team. They will create a dedicated section in protocol docs for your multisig with the registration information.

## Registration Template

```
Multisig Name: [Name]
Address: [Checksummed address]
Network: [Ethereum/Solana/etc]
Threshold: [X of Y signers]
Classification: [Impact Level] / [Operational Type]
Purpose: [Brief description]

Signers:
- [Handle/Entity]: [Address] - [Verification signature]
- [Handle/Entity]: [Address] - [Verification signature]

Controlled contracts: [List contract addresses and purposes]
On-chain roles: [Describe roles like ownable, Access Control roles (PAUSER_ROLE)]

Impact assessment:
- Financial exposure: $[amount] ([reasoning])
- Protocol impact: [description]
- Classification: [Low/Medium/High/Critical]

Operational classification: [Routine/Time-Sensitive/Emergency]

Constraining factors:
- [Smart contract limits, governance controls, etc.]

Attestation: This multisig [meets/deviates from] security standards.
[If deviation: Justification and compensating controls]

Last updated: [Date]
Updated by: [Name/Handle]
```

## Signer Verification Process

Each signer must provide a verification signature linking their identity to their address:

1. **Sign message**: "[handle/entity] intends to join [multisig address] with signer [address]"
2. **Share signature** with multisig team
3. **Update registration** with verified information

Detailed steps for collecting this information are provided in [Joining a Multisig](/multisig-for-protocols/joining-a-multisig).

**Note**: Entity affiliations are acceptable - the goal is accountability, not doxxing.

## Update Template

Use this template when making changes to signer composition:

```
Multisig Signer Update

Multisig Name: [Name]
Address: [Checksummed address]
Network: [Ethereum/Solana/etc]
Updated by: [Name/Handle]
Update Date: [Date]

Threshold Changes:
Previous: [X of Y signers]
New: [X of Y signers]

Signer Changes:
Additions:
- [Handle/Entity]: [Address] - [Verification signature]

Removals:
- [Handle/Entity]: [Address]

Current Signer Set:
- [Handle/Entity]: [Address]
- [Handle/Entity]: [Address]
- [Handle/Entity]: [Address]

Transaction: [Link to executed transaction]
```

## Documentation Requirements

### Initial Registration

- Complete registration template with all required fields
- Verification signatures from all signers
- Classification assessment from [Planning & Classification](/multisig-for-protocols/planning-and-classification)
- Submit to protocol security team

### Ongoing Maintenance

- Update documentation when signers change
- Record rationale for any threshold changes
- Update classification if operational patterns change
- Maintain current contact information

## Ongoing Management

### Regular reviews

Set periodic reminders to keep documentation current:

- **Quarterly**: Review and update protocol documentation if needed
- **After major changes**: Update when operational patterns or financial exposure changes significantly
- **Protocol updates**: Reassess if significant protocol changes affect the multisig's role

### Signer changes

Follow these procedures for adding, removing, or replacing signers:

#### Adding/Removing signers

- Maintain or increase total signer count and threshold
- Document rationale for any changes that reduce signers or threshold
- Update all documentation immediately after change

#### Replacing signers
Follow steps in [Signer Rotation](/wallet-security/secure-multisig-best-practices#signer-rotation) 

### Documentation updates

After any signer change:

- Record change rationale and date
- Communicate changes to protocol security team
- Update communication channel memberships

#### Update Template

Use the template in [Registration & Documentation → Update Template](/multisig-for-protocols/registration-and-documentation#update-template).

## Related Documents

- [Planning & Classification](/multisig-for-protocols/planning-and-classification) - How to classify your multisig
- [Joining a Multisig](/multisig-for-protocols/joining-a-multisig) - Signer verification process

