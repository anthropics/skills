# On-Chain Adoption Guide

This guide explains how protocols can register their Safe Harbor adoption on-chain. Registering ensures your adoption is
**public, verifiable, and enforceable**.

## Why On-Chain Adoption Matters

On-chain registration:

- Makes your Safe Harbor adoption **public and transparent**.
- Signals to whitehats that your protocol is officially covered under the agreement.
- Publishes your terms (scope, bounty, contacts) on-chain in a way that's **traceable and verifiable**, even if updated
later.

## How On-Chain Adoption Works

The process involves **two steps**:

1. **Deploy your AgreementV2 contract** (containing your scope details)
2. **Register the agreement** with the Safe Harbor Registry

## Three Ways to Deploy and Register

**Important Note:**

- The address that registers **represents your protocol on-chain**.
- Most protocols use **multisigs** or **DAOs** for the registration step - Be sure to set the `owner` of the agreement
to your multisig or DAO address if you are registering with them.
- The simplest workflow is to use the SEAL Self-Adoption Tool to deploy your agreement and register it with your
multisig/DAO.

### 1. SEAL Self-Adoption Website + Script/Multisig Registration

1. Navigate to the [SEAL Self-Adoption Tool](https://safeharbor.securityalliance.org/adoption).
2. Fill in your scope details (Asset Recovery Address, Assets Under Scope, Bounty Terms, etc.).
    - **WARNING**: Be sure to set the `owner` of the agreement to your multisig or DAO address if you're registering
    with them.
3. Choose one of the following:
    - **Generate an Agreement** to deploy your AgreementV2 contract via the SEAL tool
    - **Export JSON** for use in Foundry scripts
4. **Deploy your agreement** using the generated parameters
5. **Register separately** using either:
    - Foundry script (see method 3 below)
    - Multisig registration (see method 2 below)

### 2. Multisig Registration (Gnosis Safe)

If your protocol uses a multisig, you can register on-chain securely after deploying your agreement.

**Steps:**

1. **First, deploy your AgreementV2 contract**:
    - Use the SEAL Self-Adoption Tool to generate the deployment parameters
    - Deploy via the AgreementFactoryV2 using your preferred method
    - **WARNING:** Be sure to set the `owner` of the agreement to your multisig address

2. **Register with your multisig**:

    - Open your Gnosis Safe and go to the **Transaction Builder** app
    - Enter the **Safe Harbor Registry address**:
        - Default for most EVM chains: `0x1eaCD100B0546E433fbf4d773109cAD482c34686`
        - Full address list: [Registry Addresses](https://github.com/security-alliance/safe-harbor)
    - Select the method: `adoptSafeHarbor(address agreementAddress)` and input your deployed AgreementV2 contract
    address
    - Add the transaction and simulate it:
        - You should see a `SafeHarborAdoption` event with your multisig as the `entity`
    - Collect signatures and execute

### 3. Foundry Script / Custom Code

If you prefer deploying and registering via code or need custom integrations, you can use SEAL's Foundry script or write
your own.

**Using SEAL's Foundry Script:**

- Repository: [security-alliance/safe-harbor](https://github.com/security-alliance/safe-harbor)
- Script: `registry-contracts/script/v2/AdoptSafeHarborV2.s.sol`

**Steps:**

1. Generate your **scope JSON** via the SEAL tool or manually prepare it using
`registry-contracts/agreementDetailsV2.json` as a template
2. Paste the JSON into: `registry-contracts/agreementDetailsV2.json`
3. Run the script:

    - By default, the script will set the deployer as the owner of the agreement
    - You can change this by setting `AGREEMENT_OWNER` in your `.env` file to your desired owner address
    - By default, the script will not register the agreement - you can change this by setting `DEPLOY_REGISTRY` to
    `true` in your `.env` file
    - The script can handle both deployment and registration

**Manual Method:**

1. Deploy your agreement: `AgreementFactoryV2.create(AgreementDetailsV2 memory details, address registry, address
owner)`
2. Register it: `SafeHarborRegistryV2.adoptSafeHarbor(address agreementAddress)`
3. Use the deployed [Registry & Factory Addresses](https://github.com/security-alliance/safe-harbor/blob/main/README.md)

## Key Contracts

- **Agreement Factory:** Deploys AgreementV2 contracts
- **Safe Harbor Registry:** Registers adoption and makes it official
- **Deployed Addresses:** [View Registry & Factory
Addresses](https://github.com/security-alliance/safe-harbor/blob/main/README.md)

---

If you ever need help or have any questions, don't hesitate to reach out!
📬 Contact us at: [safe-harbor@securityalliance.org](mailto:safe-harbor@securityalliance.org)

---

