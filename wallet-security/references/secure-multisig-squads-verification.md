# Squads Multisig: Step-by-Step Verification
Limited tooling is available for Solana verification compared to EVM. Exercise extra caution and cross-verify with team members.

## Workflow

1) Initial Proposal (SOL transfer, token transfer, signer/threshold change)

2) Simulation

- Squads UI provides a simulation link after first signature
- Simulation is helpful for transfers; configuration changes often fail, but you can still inspect data via explorer

## SOL Transfer Verification

![SOL transfer transaction overview](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/sol-transfer-transaction-overview.png)
[Transaction Link](https://app.squads.so/squads/e4knHMRYwCTQH879dRoTUvWwKR9jy5jE52kh2iy4kL2/transactions/2sAD1s2cpN8xkDKpsjF3mgpAZ5T6Ly4Zuattr6eMzmjG)
[Simulation Link](https://explorer.solana.com/tx/inspector?signatures=%255B%25221111111111111111111111111111111111111111111111111111111111111111%2522%252C%25221111111111111111111111111111111111111111111111111111111111111111%2522%255D&message=gAIAAgZwPe7Z%252FXshAtomCcciz6nV7UMyPHih06vc7yk9ty6UoAl%252BvEzOMR3HvSFhM2GWdWNVeRQBVmsO%252BMzLyKmaMKEz7jI0LiZeXnyTOKjFEy5Th61mABykSj2asFCSBK3vw7WMKRhm0xquPpdNaEAeFg%252FN30zo7KzBfmzdI3QlkLN55QMGRm%252FlIRcy%252F%252BytunLDm%252Be8jOW7xfcSayxDmzpAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAS9ir2PAxknA4YchoA50xsGOmMh%252FMWqcxS3WgQCJFjjgQEAAUBAAAEAAQABQLAXBUABQIBAgwCAAAAgJaYAAAAAAAFAgEDDAIAAABAS0wAAAAAAAA%253D)

On the simulation page scroll down to **System Program Instruction**
![System Program Instruction details](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/system-program-instruction-details.png)
This shows the destination address for the SOL (H2p…Kr) and the Instruction Data. The instruction data can be interpreted as follows.

**Example instruction data interpretation:**
```
02 00 00 00 80 96 98 00 00 00 00 00
```

1. **Split into bytes**: `02 00 00 00 80 96 98 00 00 00 00 00`
2. **First 4 bytes (transfer type)**: `02 00 00 00` = [2, 0, 0, 0] ✅ (confirms this is a token transfer)
3. **Amount bytes (little-endian)**: `80 96 98 00 00 00 00 00` = [128, 150, 152, 0, 0, 0, 0, 0] in decimal
4. **Convert from little-endian to decimal**:
   - Little-endian means least significant byte first
   - `80 96 98 00` = `0x00989680` in big-endian hex
   - `0x00989680` = 10,000,000 in decimal
5. **Convert lamports to SOL**:
   - 1 SOL = 1,000,000,000 lamports
   - 10,000,000 lamports ÷ 1,000,000,000 = 0.01 SOL ✅

Quick verification method:
For the amount portion (`80 96 98 00 00 00 00 00`):
- Reverse the order: `00 00 00 00 00 98 96 80`
- Convert hex to decimal: `0x989680` = 10,000,000
- Divide by 1,000,000,000: 10,000,000 ÷ 1,000,000,000 = 0.01 SOL

## USDS Transfer Verification

[Transaction Link](https://app.squads.so/squads/e4knHMRYwCTQH879dRoTUvWwKR9jy5jE52kh2iy4kL2/transactions/CpPSRtvsZjhYrQwXKg72JwnLYsFQEmCkKLLA1v97ggTF)
[Simulation Link](https://explorer.solana.com/tx/inspector?signatures=%255B%25221111111111111111111111111111111111111111111111111111111111111111%2522%252C%25221111111111111111111111111111111111111111111111111111111111111111%2522%255D&message=gAIABQmMKRhm0xquPpdNaEAeFg%252FN30zo7KzBfmzdI3QlkLN55Ql%252BvEzOMR3HvSFhM2GWdWNVeRQBVmsO%252BMzLyKmaMKEzxF5adOSOc03j8RtbcEMRZfSyDhZDpj%252Bf89egzdX3712eUpW3sOB32puEK85AjoAlc8KSleU8LnaIbhD8fK9eRgMGRm%252FlIRcy%252F%252BytunLDm%252Be8jOW7xfcSayxDmzpAAAAAjJclj04kifG7PRApFI4NgwtaE5na%252FxCEBI572Nvp%252BFnuMjQuJl5efJM4qMUTLlOHrWYAHKRKPZqwUJIEre%252FDtQcHMS0dQdpx8PsoDBZizWXr6y4IWcDLrj%252Fb3LJshuCvBt324ddloZPZy%252BFGzut5rBy0he1fWzeROoz1hX7%252FAKkVxPfrULPMJ%252BJHEroegjMTe9e7y7fbwd%252BuhToyuOMfEQQEAAUBAAAEAAQABQLAXBUABQYBAgYHCQgBAQgEAwcCAQoMQEIPAAAAAAAGAbqmLEkSumVVR1a24Yy6rkkWI1IASK6g1AQ30DXoTsREAAEF))

On the simulation page scroll down to **Associated Token Program: Create Idempotent** & **Token Program Instruction**
![Token Program Instruction details](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/token-program-instruction-details.png)
This shows the destination address for the USDS in the Token Program Instruction (H2p…Kr) and the Instruction Data. The instruction data can be interpreted as follows.
```
0c 40 42 0f 00 00 00 00 00 00 06
```

1. **Split into bytes**: `0c 40 42 0f 00 00 00 00 00 00 06`
2. **First byte (instruction type)**: `0c` = 12 in decimal ✅ (confirms this is TransferChecked instruction)
3. **Amount bytes (little-endian)**: `40 42 0f 00 00 00 00 00` = [64, 66, 15, 0, 0, 0, 0, 0] in decimal
4. **Convert from little-endian to decimal**:
   - `40 42 0f 00` = `0x000f4240` in big-endian hex
   - `0x000f4240` = 1,000,000 in decimal
5. **Convert raw units to USDS**:
   - USDS has 6 decimals
   - 1,000,000 raw units ÷ 10^6 = 1.0 USDS ✅
6. **Decimals verification**: Last byte `06` = 6 decimals ✅ (correct for USDS)

## Configuration Change Verification

![Configuration change transaction overview](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/configuration-change-transaction-overview.png)
[Transaction Link](https://app.squads.so/squads/e4knHMRYwCTQH879dRoTUvWwKR9jy5jE52kh2iy4kL2/transactions/4KDPpv27fQmbWteQjSZLku8sGxNfoDqtYG4mZQp2zbiq)
Simulation does NOT seem to work for configuration changes, but we have another way we can verify it!

1. Copy the transaction ID ([4KDPpv27fQmbWteQjSZLku8sGxNfoDqtYG4mZQp2zbiq](https://explorer.solana.com/address/4KDPpv27fQmbWteQjSZLku8sGxNfoDqtYG4mZQp2zbiq?signatures=%255B%25221111111111111111111111111111111111111111111111111111111111111111%2522%252C%25221111111111111111111111111111111111111111111111111111111111111111%2522%255D&message=gAIABQmMKRhm0xquPpdNaEAeFg%252FN30zo7KzBfmzdI3QlkLN55Ql%252BvEzOMR3HvSFhM2GWdWNVeRQBVmsO%252BMzLyKmaMKEzxF5adOSOc03j8RtbcEMRZfSyDhZDpj%252Bf89egzdX3712eUpW3sOB32puEK85AjoAlc8KSleU8LnaIbhD8fK9eRgMGRm%252FlIRcy%252F%252BytunLDm%252Be8jOW7xfcSayxDmzpAAAAAjJclj04kifG7PRApFI4NgwtaE5na%252FxCEBI572Nvp%252BFnuMjQuJl5efJM4qMUTLlOHrWYAHKRKPZqwUJIEre%252FDtQcHMS0dQdpx8PsoDBZizWXr6y4IWcDLrj%252Fb3LJshuCvBt324ddloZPZy%252BFGzut5rBy0he1fWzeROoz1hX7%252FAKkVxPfrULPMJ%252BJHEroegjMTe9e7y7fbwd%252BuhToyuOMfEQQEAAUBAAAEAAQABQLAXBUABQYBAgYHCQgBAQgEAwcCAQoMQEIPAAAAAAAGAbqmLEkSumVVR1a24Yy6rkkWI1IASK6g1AQ30DXoTsREAAEF))
   1. This will take you to an 'account' page on the Solana explorer representing just this transaction
2. Click the [first transaction](https://explorer.solana.com/tx/36QYWYC9a5eCtd8QNkdjWmqUyY21wNYBNRtuQrtPqJRg1QbeL8rmVKume21VwrQRjJHZjkHVMMWA1sYWtF4wfZ6u) in the history of this 'transaction account'
3. Scroll down to **Squads Multisig Program: Config Transaction Create**
   1. Expand all fields to view the decoded transaction data

![Squads Multisig Program details](https://frameworks-static.s3.us-east-2.amazonaws.com/images/multisig-for-protocols/squads-multisig-program-details.png)

## Signing & Execution

- Sign (do not execute) and confirm expected hash on hardware wallet
- Execute after collecting all signatures
- Once all signatures are collected, execute the transaction.

