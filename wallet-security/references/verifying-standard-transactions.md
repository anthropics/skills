# Verifying Standard Transactions (EOA)

When interacting with a dApp using a standard Externally Owned Account (EOA) via a wallet, you must verify several key
components of the transaction request before signing.

## 1. Verify the Origin

- **What to check**: The URL of the website initiating the transaction request.
- **Why it's critical**: A malicious site can perfectly clone a legitimate dApp's interface to trick you into signing a
malicious transaction. Always ensure you are on the correct, official domain.

## 2. Verify the Smart Contract Address

- **What to check**: The contract address listed under a field like "Interacting With" in your wallet's transaction
prompt.
- **Why it's critical**: This is the actual on-chain address your transaction is being sent to. A malicious dApp will
substitute a fraudulent contract address here.
- **Verification Methods**:
  - **Official Documentation**: The most reliable source. Find the "Contract Addresses" or "Deployments" section in the
protocol's official documentation and confirm the address matches.
  - **Block Explorer (Etherscan, Blockscout, etc.)**: Paste the address into a block explorer. Look for verification
checkmarks, official labels, and a healthy transaction history.

## 3. Verify the Function and Parameters

- **What to check**: The function name (e.g., `depositETH`) and the parameters in the "Data" tab of your wallet.
- **Why it's critical**: This is the exact *action* you are authorizing the smart contract to perform. A malicious
transaction might look legitimate on the surface but contain a harmful function call.
- **Verification Methods**:
  - **Cross-reference with Documentation**: The protocol's developer documentation will define the function and what
each parameter represents.
  - **Scrutinize Recipient Addresses**: For any function that directs assets (e.g., `onBehalfOf`, `recipient`, `to`),
ensure the address is your own or the intended recipient.
  - **Understand Amounts**: Verify token amounts, paying attention to the number of decimals.

## 4. Sanity-Check the Network Fee (Gas)

- **What to check**: The estimated gas fee for the transaction.
- **Why it's critical**: An unusually high gas fee for a simple operation can be a red flag, potentially indicating an
inefficient or malicious contract designed to waste user funds.

---

