# Node Operation and Block Producer Setup

This guide covers running XPR Network nodes, becoming a Block Producer, and operating infrastructure.

## Overview

XPR Network runs on **Antelope/Leap** (formerly EOSIO). Node types include:

| Type | Purpose | Requires |
|------|---------|----------|
| **API Node** | Serve RPC requests | Public endpoints |
| **Block Producer** | Validate transactions, produce blocks | Registration, KYC |
| **State History** | Stream full history | Large storage |
| **Seed Node** | P2P network connectivity | Stable connection |

---

## System Requirements

### Hardware

| Component | Minimum | Recommended |
|-----------|---------|-------------|
| CPU | 4 cores | 8+ cores (high single-thread) |
| RAM | 16 GB | 32+ GB |
| Storage | 500 GB SSD | 1+ TB NVMe |
| Network | 100 Mbps | 1 Gbps |

### Software

- **OS:** Ubuntu 22.04 LTS
- **Leap Version:** 5.0.3 or later (as of Sept 2025)

Verify OS version:
```bash
lsb_release -a
```

---

## Installing Leap

### Download and Install

```bash
# Download Leap 5.0.3
wget https://github.com/AntelopeIO/leap/releases/download/v5.0.3/leap_5.0.3_amd64.deb

# Install
sudo apt install ./leap_5.0.3_amd64.deb

# Verify installation
nodeos --version
cleos --version
```

### Directory Structure

```bash
/opt/XPRMainNet/
├── config.ini          # Node configuration
├── genesis.json        # Genesis block
├── start.sh            # Startup script
├── stop.sh             # Shutdown script
├── stderr.txt          # Log output
└── data/
    ├── blocks/         # Block data
    └── state/          # Chain state
```

---

## Mainnet Node Setup

### Clone Configuration

```bash
mkdir -p /opt/XPRMainNet
cd /opt/XPRMainNet
git clone https://github.com/XPRNetwork/xpr.start.git ./
```

### Configure Node

Edit `config.ini`:

```ini
# Network identity
agent-name = "MyNodeName"
p2p-server-address = YOUR_EXTERNAL_IP:9876

# Chain database
chain-state-db-size-mb = 16384

# SECURITY: Limit connections per host to prevent connection exhaustion attacks
p2p-max-nodes-per-host = 2
max-clients = 100

# Plugins
plugin = eosio::chain_api_plugin
plugin = eosio::http_plugin
plugin = eosio::net_plugin
plugin = eosio::net_api_plugin

# HTTP settings
http-server-address = 0.0.0.0:8888
access-control-allow-origin = *

# Billing
disable-subjective-p2p-billing = false
```

### Mainnet P2P Peers (Verified January 2026)

```ini
p2p-peer-address = api.protonnz.com:9876
p2p-peer-address = proton.protonuk.io:9876
p2p-peer-address = proton.p2p.eosusa.io:9879
p2p-peer-address = proton.cryptolions.io:9876
p2p-peer-address = protonp2p.eoscafeblock.com:9130
p2p-peer-address = p2p.alvosec.com:9876
p2p-peer-address = p2p.totalproton.tech:9831
p2p-peer-address = mainnet.brotonbp.com:9876
p2p-peer-address = proton.eu.eosamsterdam.net:9103
p2p-peer-address = protonp2p.blocksindia.com:9876
p2p-peer-address = p2p-protonmain.saltant.io:9876
p2p-peer-address = protonp2p.ledgerwise.io:23877
p2p-peer-address = proton-seed.eosiomadrid.io:9876
p2p-peer-address = proton.genereos.io:9876
p2p-peer-address = proton-public.neftyblocks.com:19876
p2p-peer-address = p2p-proton.eosarabia.net:9876
p2p-peer-address = p2p.luminaryvisn.com:9876
```

### Firewall Configuration

```bash
# Open required ports
sudo ufw allow 8888/tcp   # HTTP API
sudo ufw allow 9876/tcp   # P2P
sudo ufw enable
```

### Start Node

First run (sync from genesis):
```bash
./start.sh --delete-all-blocks --genesis-json genesis.json
```

Subsequent runs:
```bash
./start.sh
```

### Monitor Node

```bash
# Watch logs
tail -f stderr.txt

# Check sync status
cleos get info

# Verify head block
curl http://localhost:8888/v1/chain/get_info | jq '.head_block_num'
```

---

## Testnet Node Setup

### Clone Testnet Configuration

```bash
mkdir -p /opt/XPRTestNet
cd /opt/XPRTestNet
git clone https://github.com/XPRNetwork/xpr-testnet.start.git ./
```

### Testnet Chain ID

```
71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd
```

### Testnet P2P Peers (Verified January 2026)

```ini
p2p-peer-address = p2p-protontest.saltant.io:9879
p2p-peer-address = testnet-p2p.alvosec.com:9878
p2p-peer-address = proton-seed-testnet.eosiomadrid.io:9877
p2p-peer-address = proton.testnet.protonuk.io:9876
p2p-peer-address = p2p.testnet.totalproton.tech:9842
p2p-peer-address = testnet.brotonbp.com:9877
p2p-peer-address = p2p-xpr-test.danemarkbp.com:9876
p2p-peer-address = tn1.protonnz.com:9876
p2p-peer-address = xpr-testnet-p2p.bloxprod.io:9875
p2p-peer-address = peer-xprtest.blocksforge.com:9876
p2p-peer-address = test.proton.p2p.eosusa.io:19879
p2p-peer-address = p2p.proton-testnet.genereos.io:9876
p2p-peer-address = protontest.eu.eosamsterdam.net:9905
p2p-peer-address = proton-testnet.cryptolions.io:9874
p2p-peer-address = testnet-p2p.xprlabs.org:9870
p2p-peer-address = p2p-testnet-proton.eosarabia.net:9876
p2p-peer-address = proton-p2p-testnet.neftyblocks.com:19876
```

### Testnet Resources

| Resource | URL |
|----------|-----|
| Explorer | https://testnet.explorer.xprnetwork.org |
| Account Creation | https://testnet.webauth.com |
| Faucet | https://testnet.resources.xprnetwork.org/faucet |

---

## Becoming a Block Producer

### Requirements

1. **Business Entity** - Must operate as a registered business
2. **KYC Verification** - Complete identity verification at https://identity.metalx.com
3. **Testnet Performance** - 14 consecutive days of block signing without interruption
4. **Performance Score** - Achieve < 0.35ms block production time
5. **Code of Conduct** - Sign the BP Code of Conduct
6. **Ownership Disclosure** - Disclose beneficial ownership

### Generate Block Signing Key

Create a dedicated key pair for block signing (separate from account keys):

```bash
# Create wallet
cleos wallet create --file wallet_pass.txt

# Generate signing key
cleos create key --to-console

# Save both public and private keys securely
```

### Register as Block Producer

```bash
cleos system regproducer YOURACCOUNT SIGNING_PUBLIC_KEY "https://yourwebsite.com" LOCATION -p YOURACCOUNT

# LOCATION = ISO 3166-1 numeric country code
# e.g., 840 = United States, 826 = United Kingdom
```

### BP Configuration

Add to `config.ini`:

```ini
# Block producer settings
producer-name = youraccount
signature-provider = PUB_KEY=KEY:PRIV_KEY

# Producer plugin
plugin = eosio::producer_plugin
plugin = eosio::producer_api_plugin

# Performance
max-transaction-time = 150
abi-serializer-max-time-ms = 2000
```

### Security Hardening

```ini
# Restrict producer API to localhost only
http-server-address = 127.0.0.1:8888

# Or use firewall to block external access to producer endpoints
```

### CPU Performance

Set CPU governor to performance mode:

```bash
# Check current governor
cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor

# Set to performance
echo "performance" | sudo tee /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor

# Make persistent (add to /etc/rc.local or systemd service)
```

---

## API Node Setup

For public API nodes serving dApps:

### Configuration

```ini
# API plugins
plugin = eosio::chain_api_plugin
plugin = eosio::http_plugin
plugin = eosio::net_plugin

# Enable state history for Hyperion
plugin = eosio::state_history_plugin
state-history-endpoint = 0.0.0.0:8080
trace-history = true
chain-state-history = true

# HTTP settings
http-server-address = 0.0.0.0:8888
http-max-response-time-ms = 100
http-validate-host = false
access-control-allow-origin = *
access-control-allow-headers = *

# Increase limits for API
max-clients = 150
abi-serializer-max-time-ms = 2000
```

### Reverse Proxy (Nginx)

```nginx
upstream nodeos {
    server 127.0.0.1:8888;
}

server {
    listen 443 ssl http2;
    server_name api.yournode.com;

    ssl_certificate /etc/letsencrypt/live/api.yournode.com/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/api.yournode.com/privkey.pem;

    location / {
        proxy_pass http://nodeos;
        proxy_http_version 1.1;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;

        # Rate limiting
        limit_req zone=api burst=20 nodelay;
    }
}
```

---

## State History / Hyperion Setup

For running a full history node with Hyperion:

### State History Plugin

```ini
plugin = eosio::state_history_plugin
state-history-endpoint = 0.0.0.0:8080
trace-history = true
chain-state-history = true
```

### Hyperion Installation

See: https://hyperion.docs.eosrio.io/

Key components:
- Elasticsearch (data storage)
- RabbitMQ (message queue)
- Redis (caching)
- Hyperion Indexer
- Hyperion API

---

## Snapshots and Fast Sync

### Download Snapshot

Instead of syncing from genesis, use a recent snapshot:

```bash
# Download snapshot (example from CryptoLions)
wget https://backup.cryptolions.io/ProtonMainNet/snapshots/latest-snapshot.bin.zst

# Decompress
zstd -d latest-snapshot.bin.zst

# Start with snapshot
nodeos --snapshot latest-snapshot.bin
```

### Create Snapshot

```bash
curl -X POST http://127.0.0.1:8888/v1/producer/create_snapshot
```

---

## Monitoring

### Health Checks

```bash
#!/bin/bash
# health_check.sh

# Check if nodeos is running
if ! pgrep -x "nodeos" > /dev/null; then
    echo "nodeos not running!"
    exit 1
fi

# Check head block age
HEAD_TIME=$(curl -s http://localhost:8888/v1/chain/get_info | jq -r '.head_block_time')
HEAD_EPOCH=$(date -d "$HEAD_TIME" +%s)
NOW_EPOCH=$(date +%s)
AGE=$((NOW_EPOCH - HEAD_EPOCH))

if [ $AGE -gt 30 ]; then
    echo "Node is $AGE seconds behind!"
    exit 1
fi

echo "Node healthy, $AGE seconds behind head"
exit 0
```

### Prometheus Metrics

Use nodeos metrics endpoint or community exporters:

```yaml
# prometheus.yml
scrape_configs:
  - job_name: 'nodeos'
    static_configs:
      - targets: ['localhost:8888']
```

### Alerting

Set up alerts for:
- Node down
- Block production missed (for BPs)
- Sync lag > 30 seconds
- Disk space low
- Memory usage high

---

## Maintenance

### Graceful Shutdown

```bash
./stop.sh
# or
pkill -SIGINT nodeos
```

### Replay Blockchain

If chain state corrupted:

```bash
nodeos --replay-blockchain
```

### Hard Replay

If blocks corrupted:

```bash
nodeos --hard-replay-blockchain
```

### Clean Start

Delete all data and resync:

```bash
./start.sh --delete-all-blocks --genesis-json genesis.json
```

---

## Quick Reference

### Chain IDs

| Network | Chain ID |
|---------|----------|
| Mainnet | `384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0` |
| Testnet | `71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd` |

### Default Ports

| Port | Service |
|------|---------|
| 8888 | HTTP API |
| 9876 | P2P |
| 8080 | State History |

### Useful Commands

```bash
# Node info
cleos get info

# Account info
cleos get account ACCOUNT

# Table query
cleos get table CODE SCOPE TABLE

# Push transaction
cleos push action CONTRACT ACTION 'DATA' -p AUTH

# BP schedule
cleos get schedule

# Producer info
cleos system listproducers
```

### Repositories

| Network | Repository |
|---------|------------|
| Mainnet | https://github.com/XPRNetwork/xpr.start |
| Testnet | https://github.com/XPRNetwork/xpr-testnet.start |

### Support Channels

- **Telegram:** XPR Network Validators
- **Discord:** #validators channel
- **Help Desk:** https://help.xprnetwork.org
