# NFTs and AtomicAssets on XPR Network

This guide covers NFT development on XPR Network using the AtomicAssets standard - the primary NFT framework for EOSIO-based chains.

## AtomicAssets Overview

AtomicAssets is a RAM-efficient NFT standard developed by pink.network. Key benefits:

- **RAM efficient**: 151 bytes per asset, dApp pays RAM (not users)
- **No claim required**: Transfers are instant, no user action needed
- **Built-in trading**: Native two-sided trade offers
- **Notification hooks**: Assets can trigger smart contract logic
- **Token backing**: NFTs can be backed by fungible tokens

---

## Core Concepts Hierarchy

```
Collection
    └── Schema (defines data structure)
            └── Template (reusable data, optional)
                    └── Asset (the actual NFT)
```

### Collections

Top-level containers that group related NFTs. Authorization is per-collection, not per-author.

| Field | Description |
|-------|-------------|
| `collection_name` | Unique name (1-12 chars, a-z, 1-5) |
| `author` | Creator account |
| `allow_notify` | Enable contract notifications |
| `authorized_accounts` | Accounts that can create assets |
| `notify_accounts` | Accounts to notify on transfers |
| `market_fee` | Marketplace fee percentage |

### Schemas

Define the data structure for NFTs in a collection.

| Field | Description |
|-------|-------------|
| `schema_name` | Unique within collection |
| `format` | Array of `{name, type}` attribute definitions |

Supported types: `int8`, `int16`, `int32`, `int64`, `uint8`, `uint16`, `uint32`, `uint64`, `float`, `double`, `string`, `image`, `ipfs`, `bool`

### Templates

Reusable data containers - multiple assets can share one template. This saves RAM when minting many similar NFTs.

| Field | Description |
|-------|-------------|
| `template_id` | Auto-generated ID |
| `schema_name` | Schema this template uses |
| `immutable_data` | Fixed data (cannot be changed) |
| `transferable` | Can assets be transferred? |
| `burnable` | Can assets be burned? |
| `max_supply` | Maximum mintable (0 = unlimited) |

### Assets

The actual NFTs owned by users.

| Field | Description |
|-------|-------------|
| `asset_id` | Unique 64-bit ID |
| `collection_name` | Parent collection |
| `schema_name` | Schema defining structure |
| `template_id` | Optional template reference |
| `immutable_data` | Fixed at creation |
| `mutable_data` | Can be updated by authorized accounts |

---

## API Endpoints

### AtomicAssets API

| Network | Endpoint | Provider |
|---------|----------|----------|
| Mainnet | `https://proton.api.atomicassets.io` | Pink.gg |
| Mainnet | `https://aa-xprnetwork-main.saltant.io` | Saltant |
| Testnet | `https://test.proton.api.atomicassets.io` | Pink.gg |
| Testnet | `https://aa-xprnetwork-test.saltant.io` | Saltant |

### AtomicMarket API (Marketplace)

| Network | Endpoint |
|---------|----------|
| Mainnet | `https://proton.api.atomicassets.io` |

---

## Querying NFTs

### Get Assets Owned by Account

```typescript
async function getOwnedAssets(owner: string, collection?: string) {
  const params = new URLSearchParams({
    owner,
    limit: '100',
    order: 'desc',
    sort: 'asset_id'
  });

  if (collection) {
    params.set('collection_name', collection);
  }

  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/assets?${params}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Collection Info

```typescript
async function getCollection(collectionName: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/collections/${collectionName}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Templates in Collection

```typescript
async function getTemplates(collectionName: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/templates?collection_name=${collectionName}&limit=100`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Schemas in Collection

```typescript
async function getSchemas(collectionName: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/schemas?collection_name=${collectionName}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Specific Asset

```typescript
async function getAsset(assetId: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/assets/${assetId}`
  );
  const { data } = await response.json();
  return data;
}
```

---

## Marketplace Queries

### Get Active Sales

```typescript
async function getSales(collection?: string) {
  const params = new URLSearchParams({
    state: '1',  // 1 = listed/active
    limit: '100',
    order: 'desc',
    sort: 'created'
  });

  if (collection) {
    params.set('collection_name', collection);
  }

  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicmarket/v1/sales?${params}`
  );
  const { data } = await response.json();
  return data;
}
```

### Get Floor Price for Template

```typescript
async function getTemplateFloorPrice(templateId: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicmarket/v1/sales?` +
    `template_id=${templateId}&state=1&limit=1&order=asc&sort=price`
  );
  const { data } = await response.json();
  return data[0]?.price ?? null;
}
```

### Get Sales History

```typescript
async function getSalesHistory(assetId: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicmarket/v1/sales?` +
    `asset_id=${assetId}&state=3&limit=10`  // state 3 = sold
  );
  const { data } = await response.json();
  return data;
}
```

---

## Creating NFTs (Transactions)

### 1. Create Collection

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createcol',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    author: author,
    collection_name: 'mycollection',
    allow_notify: true,
    authorized_accounts: [author],
    notify_accounts: [],
    market_fee: 0.05,  // 5%
    data: []  // Collection metadata
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 2. Create Schema

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createschema',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_creator: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    schema_format: [
      { name: 'name', type: 'string' },
      { name: 'image', type: 'ipfs' },
      { name: 'description', type: 'string' },
      { name: 'rarity', type: 'string' },
      { name: 'power', type: 'uint32' }
    ]
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 3. Create Template

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'createtempl',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_creator: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    transferable: true,
    burnable: true,
    max_supply: 1000,  // 0 = unlimited
    immutable_data: [
      { key: 'name', value: ['string', 'Epic Sword'] },
      { key: 'image', value: ['string', 'QmXxx...'] },  // IPFS hash
      { key: 'description', value: ['string', 'A legendary weapon'] },
      { key: 'rarity', value: ['string', 'epic'] },
      { key: 'power', value: ['uint32', 150] }
    ]
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 4. Mint Asset

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'mintasset',
  authorization: [{ actor: author, permission: 'active' }],
  data: {
    authorized_minter: author,
    collection_name: 'mycollection',
    schema_name: 'myschema',
    template_id: 12345,  // From createtempl, or -1 for no template
    new_asset_owner: recipient,
    immutable_data: [],  // Additional immutable data
    mutable_data: [],    // Mutable data (can be updated later)
    tokens_to_back: []   // Optional token backing
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### 5. Transfer Asset

```typescript
const actions = [{
  account: 'atomicassets',
  name: 'transfer',
  authorization: [{ actor: owner, permission: 'active' }],
  data: {
    from: owner,
    to: recipient,
    asset_ids: ['1099512345678'],  // Array of asset IDs
    memo: 'Gift for you!'
  }
}];

await session.transact({ actions }, { broadcast: true });
```

---

## Marketplace Actions

### List Asset for Sale

```typescript
const actions = [{
  account: 'atomicmarket',
  name: 'announcesale',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    seller: seller,
    asset_ids: ['1099512345678'],
    listing_price: '100.0000 XPR',
    settlement_symbol: '4,XPR',
    maker_marketplace: ''  // Optional marketplace account
  }
},
{
  account: 'atomicassets',
  name: 'createoffer',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    sender: seller,
    recipient: 'atomicmarket',
    sender_asset_ids: ['1099512345678'],
    recipient_asset_ids: [],
    memo: 'sale'
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### Cancel Sale

```typescript
const actions = [{
  account: 'atomicmarket',
  name: 'cancelsale',
  authorization: [{ actor: seller, permission: 'active' }],
  data: {
    sale_id: 12345
  }
}];

await session.transact({ actions }, { broadcast: true });
```

### Purchase Asset

```typescript
const actions = [{
  account: 'eosio.token',
  name: 'transfer',
  authorization: [{ actor: buyer, permission: 'active' }],
  data: {
    from: buyer,
    to: 'atomicmarket',
    quantity: '100.0000 XPR',
    memo: 'deposit'
  }
},
{
  account: 'atomicmarket',
  name: 'purchasesale',
  authorization: [{ actor: buyer, permission: 'active' }],
  data: {
    buyer: buyer,
    sale_id: 12345,
    intended_delphi_median: 0,
    taker_marketplace: ''
  }
}];

await session.transact({ actions }, { broadcast: true });
```

---

## Smart Contract Integration

### Receiving NFT Notifications

To have your contract notified when assets are transferred:

1. Add your contract to collection's `notify_accounts`
2. Handle the notification in your contract:

```typescript
@action("transfer", notify)
onNFTTransfer(
  from: Name,
  to: Name,
  asset_ids: u64[],
  memo: string
): void {
  // Only process transfers TO this contract
  if (to != this.receiver) return;

  // Process each asset
  for (let i = 0; i < asset_ids.length; i++) {
    const assetId = asset_ids[i];
    // Handle the received NFT
    this.processReceivedNFT(from, assetId, memo);
  }
}
```

### Querying Assets On-Chain

```typescript
// Query atomicassets tables directly
const { rows } = await rpc.get_table_rows({
  code: 'atomicassets',
  scope: owner,  // Owner account as scope
  table: 'assets',
  limit: 100
});
```

---

## Data Serialization Format

AtomicAssets uses a custom serialization format for `immutable_data` and `mutable_data`:

```typescript
// Format: Array of { key: string, value: [type, data] }

const data = [
  { key: 'name', value: ['string', 'My NFT'] },
  { key: 'image', value: ['string', 'QmXxxIPFSHash'] },
  { key: 'power', value: ['uint32', 100] },
  { key: 'is_special', value: ['uint8', 1] }  // boolean as uint8
];
```

### Type Mapping

| Schema Type | Serialization Type |
|-------------|-------------------|
| `string` | `['string', 'value']` |
| `ipfs` | `['string', 'QmHash']` |
| `image` | `['string', 'url_or_ipfs']` |
| `uint8` - `uint64` | `['uint8', number]` etc. |
| `int8` - `int64` | `['int8', number]` etc. |
| `float` | `['float32', number]` |
| `double` | `['float64', number]` |
| `bool` | `['uint8', 0 or 1]` |

---

## Common Patterns

### Check if User Owns Asset

```typescript
async function userOwnsAsset(owner: string, assetId: string): Promise<boolean> {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/assets/${assetId}`
  );
  const { data } = await response.json();
  return data?.owner === owner;
}
```

### Get All Assets with Metadata

```typescript
async function getAssetsWithMetadata(owner: string) {
  const response = await fetch(
    `https://proton.api.atomicassets.io/atomicassets/v1/assets?owner=${owner}&limit=100`
  );
  const { data } = await response.json();

  return data.map(asset => ({
    id: asset.asset_id,
    name: asset.data?.name ?? asset.template?.immutable_data?.name,
    image: asset.data?.image ?? asset.template?.immutable_data?.image,
    collection: asset.collection.collection_name,
    schema: asset.schema.schema_name,
    template_id: asset.template?.template_id,
    ...asset.data
  }));
}
```

### Batch Mint Multiple Assets

```typescript
async function batchMint(
  author: string,
  collection: string,
  schema: string,
  templateId: number,
  recipients: string[]
) {
  const actions = recipients.map(recipient => ({
    account: 'atomicassets',
    name: 'mintasset',
    authorization: [{ actor: author, permission: 'active' }],
    data: {
      authorized_minter: author,
      collection_name: collection,
      schema_name: schema,
      template_id: templateId,
      new_asset_owner: recipient,
      immutable_data: [],
      mutable_data: [],
      tokens_to_back: []
    }
  }));

  // Note: Transaction size limits apply (~100 mints per tx)
  await session.transact({ actions }, { broadcast: true });
}
```

---

## IPFS for NFT Media

Store images and metadata on IPFS:

### Pinata (Recommended)

```typescript
async function uploadToIPFS(file: File): Promise<string> {
  const formData = new FormData();
  formData.append('file', file);

  const response = await fetch('https://api.pinata.cloud/pinning/pinFileToIPFS', {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${PINATA_JWT}`
    },
    body: formData
  });

  const { IpfsHash } = await response.json();
  return IpfsHash;  // Use this as 'image' value
}
```

### IPFS Gateways

| Gateway | URL Pattern |
|---------|-------------|
| Pinata | `https://gateway.pinata.cloud/ipfs/{hash}` |
| Cloudflare | `https://cloudflare-ipfs.com/ipfs/{hash}` |
| IPFS.io | `https://ipfs.io/ipfs/{hash}` |

---

## Fees and Costs

### RAM Costs

| Operation | RAM (bytes) |
|-----------|-------------|
| Create collection | ~300 |
| Create schema | ~150 + attributes |
| Create template | ~200 + data size |
| Mint asset | ~151 + data size |

RAM is paid by the minter/creator, not the recipient.

### Marketplace Fees

- **Collection fee**: Set by collection creator (typically 2-10%)
- **Marketplace fee**: Set by marketplace (typically 1-2%)
- Fees are taken from sale price when asset sells

---

## Resources

- **AtomicAssets Docs**: https://github.com/pinknetworkx/atomicassets-contract
- **AtomicMarket Docs**: https://github.com/pinknetworkx/atomicmarket-contract
- **API Documentation**: https://proton.api.atomicassets.io/docs
- **XPR Market Reference**: https://github.com/XPRNetwork/xpr-market
