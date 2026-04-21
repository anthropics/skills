# Hardware Wallet Guide

## Recommended Devices

### Ledger (Nano S Plus, Nano X, Stax)
- Secure element chip
- Wide token support
- Bluetooth on Nano X/Stax (convenience vs. air-gap tradeoff)
- Ledger Live software for management

### Trezor (Model One, Model T, Safe 3)
- Open source firmware
- No secure element (different security model)
- Passphrase support for hidden wallets
- Trezor Suite software

### Other Options
- GridPlus Lattice1 (larger screen, card-based)
- Keystone (air-gapped, QR code signing)
- BitBox02 (Swiss-made, minimalist)

## Setup Best Practices

1. **Buy direct from manufacturer** - Never secondhand or Amazon
2. **Verify tamper-evident packaging** - Check seals are intact
3. **Generate seed on device** - Never import a seed someone gave you
4. **Write seed on paper immediately** - Don't skip this step
5. **Verify seed backup** - Use device's recovery check feature
6. **Set a strong PIN** - Not birthday, not sequential
7. **Update firmware** - Before storing significant funds

## Operational Security

### Do
- Store device in secure location when not in use
- Verify addresses on device screen, not computer
- Use official software only (Ledger Live, Trezor Suite)
- Keep firmware updated

### Don't
- Enter seed phrase on any website ever
- Store seed digitally anywhere
- Use on public or shared computers
- Ignore verification prompts
- Rush through signing

## Common Attacks to Know

### Supply Chain
- Compromised devices with pre-generated seeds
- **Defense**: Buy direct, verify packaging, generate fresh seed

### Phishing
- Fake Ledger/Trezor emails requesting seed
- **Defense**: Manufacturer will NEVER ask for seed

### Physical Theft
- Device stolen, PIN brute-forced
- **Defense**: Strong PIN, consider passphrase (25th word)

### Evil Maid
- Device tampered while unattended
- **Defense**: Secure storage, verify firmware on boot

## Recovery Scenarios

### Lost Device
1. Buy new hardware wallet
2. Restore using seed phrase backup
3. Funds are safe if seed is secure

### Forgotten PIN
1. Device wipes after failed attempts (usually 3-10)
2. Restore with seed phrase
3. This is why seed backup is critical

### Compromised Seed
1. Immediately transfer funds to new wallet
2. Generate completely new seed
3. Investigate how compromise occurred
