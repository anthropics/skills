# Implementation Checklist

This checklist ensures all multisig participants have the knowledge and skills necessary for secure operations. Complete all applicable sections before beginning multisig operations.

## For Multisig Administrators

### Planning & Setup

- [ ] I have classified my multisig using the impact and operational framework from [Planning & Classification](/multisig-for-protocols/planning-and-classification)
- [ ] I have selected appropriate thresholds based on the classification guidance
- [ ] I have identified and verified all signers for the multisig
- [ ] I have deployed the multisig with correct configuration
- [ ] I have set up required modules (eg. allowance module to rescue assets)

### Documentation & Communication

- [ ] I have classified and documented the new multisig using templates from [Registration & Documentation](/multisig-for-protocols/registration-and-documentation)
- [ ] I have set up primary and backup communication channels per [Communication Setup](/multisig-for-protocols/communication-setup)
- [ ] I have tested emergency notification procedures
- [ ] I have documented emergency contact information

### Ongoing Management

- [ ] I have established procedures for regular reviews and updates per [Registration & Documentation](/multisig-for-protocols/registration-and-documentation)
- [ ] I have set up backup infrastructure and tested alternative UIs per [Backup Signing & Infrastructure](/multisig-for-protocols/backup-signing-and-infrastructure)
- [ ] I have verified all signers have completed training requirements
- [ ] I understand signer rotation procedures for my multisig type

## For Signers

### Hardware & Security Setup

- [ ] I have purchased recommended hardware wallet from authorized source per [Hardware Wallet Setup](/wallet-security/intermediates-&-medium-funds)
- [ ] I have set up my hardware wallet with proper firmware and PIN
- [ ] I have created and tested backup hardware wallet with same seed
- [ ] I have stored my seed phrase securely using approved methods from [Seed Phrase Management](/wallet-security/seed-phrase-management)
- [ ] I have created dedicated accounts for each multisig I'm signing for

### Operational Readiness

- [ ] I have joined multisig communication channels (primary and backup) per [Communication Setup](/multisig-for-protocols/communication-setup)
- [ ] I have verified my signer address using the required signature process from [Joining a Multisig](/multisig-for-protocols/joining-a-multisig)
- [ ] I understand my multisig's classification and response time requirements
- [ ] I have completed a test transaction with the multisig team

### Transaction Verification

- [ ] I can use approved verification tools (Safe CLI Utils, OpenZeppelin SafeUtils for EVM) from [Tools & Resources → Transaction Verification](/wallet-security/tools-&-resources#transaction-verification)
- [ ] I understand how to verify transaction hashes before signing
- [ ] I can decode and verify transaction details (amounts, recipients, contract calls)
- [ ] I have practiced verifying both simple transfers and complex transactions

### Emergency Preparedness

- [ ] I have downloaded backup UIs (Eternal Safe for EVM, Squads public client for Solana) per [Backup Signing & Infrastructure](/multisig-for-protocols/backup-signing-and-infrastructure)
- [ ] I know how to sign transactions when primary UI is down per [Backup Signing & Infrastructure](/multisig-for-protocols/backup-signing-and-infrastructure)
- [ ] I understand emergency procedures for key compromise and communication failures per [Emergency Procedures](/multisig-for-protocols/emergency-procedures)
- [ ] I have tested backup communication methods with my team
- [ ] I know who to contact for security incidents and emergencies per [Incident Reporting](/multisig-for-protocols/incident-reporting)

### Personal Security

- [ ] I have enabled 2FA on all accounts with approved methods (YubiKey preferred) per [Personal Security (OpSec)](/multisig-for-protocols/personal-security-opsec)
- [ ] I use dedicated devices or accounts for multisig operations when required
- [ ] I have implemented travel security procedures appropriate for my risk level
- [ ] I understand incident reporting procedures for security concerns

### Compliance

- [ ] I have read and understand all sections of this security framework
- [ ] I understand my specific role requirements based on multisig classification
- [ ] I know how to properly offboard when leaving a multisig role per [Offboarding](/multisig-for-protocols/offboarding)
- [ ] I commit to following these security procedures and reporting any deviations

## Specialized Training by Use Case

### Emergency Response Multisigs

Additional requirements from [Use Case Specific Requirements](/multisig-for-protocols/use-case-specific-requirements):

- [ ] I understand 24/7 availability requirements
- [ ] I have participated in emergency simulation drills
- [ ] I know how to respond to emergency paging
- [ ] I understand streamlined verification procedures for emergencies

### Treasury Multisigs

- [ ] I understand allowance module configuration and purpose
- [ ] I know governance rescue procedures
- [ ] I understand financial reporting requirements

### Smart Contract Control Multisigs

- [ ] I understand timelock configuration per [Use Case Specific Requirements → Timelock Configuration](/multisig-for-protocols/use-case-specific-requirements#timelock-configuration)
- [ ] I know how to verify staged transactions
- [ ] I understand higher threshold requirements for upgrades

## Practical Skills Assessment

### Transaction Verification (EVM)

- [ ] I can successfully verify a Safe transaction hash using CLI tools
- [ ] I can decode transaction calldata and identify recipients and amounts
- [ ] I can identify risky transaction types and warnings
- [ ] I can verify nested Safe transactions if applicable

### Transaction Verification (Solana)

- [ ] I can analyze Solana transaction instruction data
- [ ] I can convert hex values to decimal for amount verification
- [ ] I can identify different transaction types (SOL transfer, token transfer, config changes)

### Emergency Procedures

- [ ] I can access backup UIs and complete a transaction
- [ ] I can contact team via backup communication channels
- [ ] I know how to report key compromise immediately
- [ ] I can execute identity verification procedures if needed

### Tool Proficiency

- [ ] I am comfortable using my hardware wallet for signing
- [ ] I can navigate backup block explorers
- [ ] I can use alternative RPC endpoints
- [ ] I understand how to manually simulate transactions

## Documentation Review

### Required Reading Completed

- [ ] [Secure Multisig Best Practices](/wallet-security/secure-multisig-best-practices) - Core requirements for all multisigs
- [ ] [Hardware Wallet Setup](/wallet-security/intermediates-&-medium-funds) - Device security requirements
- [ ] [Seed Phrase Management](/wallet-security/seed-phrase-management) - Key protection procedures
- [ ] [Safe Multisig: Step-by-Step Verification](/wallet-security/secure-multisig-safe-verification) - Signing procedures
- [ ] [Emergency Procedures](/multisig-for-protocols/emergency-procedures) - Crisis response protocols
- [ ] [Personal Security (OpSec)](/multisig-for-protocols/personal-security-opsec) - Account and device security

### Role-Specific Documentation

**For Administrators:**

- [ ] [Planning & Classification](/multisig-for-protocols/planning-and-classification)
- [ ] [Setup & Configuration](/multisig-for-protocols/setup-and-configuration)
- [ ] [Registration & Documentation](/multisig-for-protocols/registration-and-documentation)
- [ ] [Communication Setup](/multisig-for-protocols/communication-setup)
- [ ] [Registration & Documentation](/multisig-for-protocols/registration-and-documentation)

**For Specialized Use Cases:**

- [ ] [Use Case Specific Requirements](/multisig-for-protocols/use-case-specific-requirements)
- [ ] [Backup Signing & Infrastructure](/multisig-for-protocols/backup-signing-and-infrastructure)
- [ ] [Use Case Specific Requirements → Timelock Configuration](/multisig-for-protocols/use-case-specific-requirements#timelock-configuration) (if applicable)

## Certification and Acknowledgment

### Training Completion

- [ ] I have completed all applicable training requirements
- [ ] I have successfully demonstrated practical skills
- [ ] I understand the security implications of my role
- [ ] I acknowledge my responsibilities as a multisig participant

### Ongoing Commitment

- [ ] I commit to following all security procedures outlined in this framework
- [ ] I will report any security incidents or concerns promptly
- [ ] I will participate in regular training updates and refreshers
- [ ] I will maintain the required level of security for my role

### Trainer Verification (if applicable)

**For organizations requiring formal training:**

Trainer: _________________ Date: _________________

Trainee has demonstrated competency in:
- [ ] Transaction verification procedures
- [ ] Emergency response protocols
- [ ] Security best practices
- [ ] Role-specific requirements

**Signature:** _________________

## Refresher Training Schedule

### Regular Updates

- **Monthly**: Review emergency procedures and contact information
- **Quarterly**: Practice backup system usage and emergency drills
- **Annually**: Complete full framework review and updates
- **As needed**: Training on new tools, procedures, or threats

### Trigger Events

Additional training required after:

- Framework updates or changes
- Security incidents affecting the team
- New tool adoption
- Role changes or additional responsibilities

## Related Documents

All documents in this framework serve as training materials. Refer to individual documents for detailed procedures and requirements specific to your role.

