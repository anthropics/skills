# Safe Harbor Adoption Checklist

## Pre-Adoption Requirements

### Assess Readiness
- [ ] Protocol has deployed contracts on mainnet
- [ ] Security contact channels established
- [ ] Secure multisig or governance wallet for recovery address
- [ ] Bug bounty program active (recommended but not required)
- [ ] Team available to respond during incidents

### Gather Information
- [ ] List all contract addresses to be covered
- [ ] Identify deployer/factory addresses (if applicable)
- [ ] Document all chains where protocol operates
- [ ] Determine bounty structure
- [ ] Decide on identity verification requirements

---

## Step 1: Define Scope

### Core Scope Elements

**Asset Recovery Address**
- Address: _______________
- Type: [ ] Gnosis Safe [ ] Governance Contract [ ] Other
- Can handle large inflows: [ ] Yes [ ] No

**Security Contacts** (minimum 2 channels)
- Email: _______________
- Signal: _______________
- Telegram: _______________
- Other: _______________

**Assets Under Scope**

| Chain | Address | Scope Type | Description |
|-------|---------|------------|-------------|
| | | [ ] All [ ] ExistingOnly [ ] FutureOnly [ ] None | |
| | | [ ] All [ ] ExistingOnly [ ] FutureOnly [ ] None | |
| | | [ ] All [ ] ExistingOnly [ ] FutureOnly [ ] None | |

### Bounty Terms

| Parameter | Value |
|-----------|-------|
| Bounty Percentage | ___% (recommend 10%) |
| Bounty Cap (USD) | $_______ |
| Aggregate Bounty Cap | $_______ (or N/A) |
| Retainable | [ ] True [ ] False |

**Note**: If Aggregate Cap is set, Retainable must be False

### Identity Verification
- [ ] Anonymous (no KYC)
- [ ] Pseudonymous
- [ ] Named (KYC required)

**If Named, diligence requirements:**
```
[Protocol Name] requires all eligible whitehats to undergo Know Your
Customer (KYC) verification and be screened against global sanctions
lists, including US, UK, and EU regulations. This process ensures that
all bounty recipients are compliant with legal and regulatory standards
before qualifying for payment.
```

---

## Step 2: DAO Proposal (If Applicable)

### Prepare Proposal
- [ ] Draft proposal using SEAL DAO template
- [ ] Include scope definition from Step 1
- [ ] Specify on-chain adoption parameters
- [ ] Set DAO address as agreement owner

### Governance Process
- [ ] Submit temperature check (if required)
- [ ] Formal proposal submitted
- [ ] Voting period completed
- [ ] Proposal passed: [ ] Yes [ ] No

**Proposal Link**: _______________
**Vote Result**: _______________

---

## Step 3: On-Chain Registration

### Create Agreement Contract
- [ ] Deploy AgreementV2 contract with scope parameters
- [ ] Set owner to DAO/governance address (if applicable)
- [ ] Verify contract on block explorer

**Agreement Contract Address**: _______________

### Register in Safe Harbor Registry
- [ ] Call registry registration function
- [ ] Include agreement contract address
- [ ] Transaction confirmed

**Registry Transaction**: _______________

### Verify Registration
- [ ] Check registration on safeharbor.securityalliance.org
- [ ] Scope details display correctly
- [ ] Bounty terms accurate

---

## Step 4: Update Documentation

### Terms of Service
- [ ] Add Safe Harbor language to TOS
- [ ] Reference adoption date
- [ ] Link to agreement

**TOS Update Location**: _______________

### Documentation Site
Add to Security/Bug Bounty section:
```
This protocol has adopted the SEAL Safe Harbor Agreement for Whitehats,
which empowers approved security researchers to intervene during active
exploits to rescue funds. Full adoption details, scope, and bounty terms
are publicly available at [LINK].
```

- [ ] Documentation updated
- [ ] Link to registry listing included

---

## Step 5: Public Announcement

### Prepare Announcement
- [ ] Draft announcement copy
- [ ] Include key details (bounty terms, protected assets)
- [ ] Mention adopter community (Uniswap, Balancer, etc.)

### Distribute
- [ ] Twitter/X announcement posted
- [ ] Discord announcement posted
- [ ] Governance forum update posted
- [ ] Blog post published (optional)

### Coordinate with SEAL
- [ ] Contact safe-harbor@securityalliance.org
- [ ] SEAL co-announcement (if desired)
- [ ] Listed on Safe Harbor adopters page

---

## Post-Adoption Maintenance

### Ongoing Tasks
- [ ] Monitor security contact channels
- [ ] Update scope when deploying new contracts
- [ ] Review bounty terms annually
- [ ] Maintain recovery address security

### Trigger Points for Updates
- New chain deployments
- New contract factories
- Changes to governance structure
- Bug bounty program changes
- Security contact changes

---

## Emergency Procedures

### If Exploit Occurs
1. Monitor security channels for whitehat contact
2. Verify whitehat followed Safe Harbor requirements
3. Confirm funds received at recovery address
4. Process bounty payment per terms
5. Coordinate public communication

### Response Timeline
| Action | Timeframe |
|--------|-----------|
| Whitehat rescue | During active exploit |
| Whitehat contact | Within 6 hours |
| Fund return | Within 72 hours |
| Bounty payment | Per terms (post-KYC if required) |

---

## Resources

**SEAL Support**: safe-harbor@securityalliance.org

**Templates**:
- DAO Scope Template: [Google Doc Link]
- Non-DAO Scope Template: [Google Doc Link]

**Registry**: safeharbor.securityalliance.org

**Legal Agreement**: [IPFS Link]
