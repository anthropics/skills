# Real-Time Events and Notifications

This guide covers listening for blockchain events, streaming data, and building notification systems on XPR Network.

## Overview

XPR Network provides several ways to get real-time updates:

| Method | Use Case | Latency |
|--------|----------|---------|
| **Hyperion Streaming** | Action/delta streams | ~1-2 seconds |
| **Polling** | Simple integrations | 1-30 seconds |
| **State History Plugin** | Full node operators | Real-time |

---

## Hyperion Streaming API

Hyperion provides WebSocket-based streaming for real-time action and delta notifications.

### Endpoint

```
wss://proton.eosusa.io/stream
```

### Stream Actions

Listen for specific contract actions in real-time:

```typescript
import WebSocket from 'ws';

interface StreamMessage {
  type: 'action' | 'delta';
  content: any;
}

class HyperionStream {
  private ws: WebSocket | null = null;
  private endpoint = 'wss://proton.eosusa.io/stream';

  connect(): Promise<void> {
    return new Promise((resolve, reject) => {
      this.ws = new WebSocket(this.endpoint);

      this.ws.on('open', () => {
        console.log('Connected to Hyperion stream');
        resolve();
      });

      this.ws.on('error', (error) => {
        console.error('Stream error:', error);
        reject(error);
      });

      this.ws.on('close', () => {
        console.log('Stream disconnected');
        this.reconnect();
      });
    });
  }

  // Subscribe to contract actions
  subscribeActions(contract: string, action: string, callback: (data: any) => void): void {
    if (!this.ws) throw new Error('Not connected');

    // Send subscription request
    this.ws.send(JSON.stringify({
      type: 'action_stream',
      req_id: `${contract}:${action}`,
      data: {
        contract,
        action,
        start_from: 'head'  // Start from current block
      }
    }));

    // Handle messages
    this.ws.on('message', (data: string) => {
      const message: StreamMessage = JSON.parse(data);
      if (message.type === 'action') {
        callback(message.content);
      }
    });
  }

  // Subscribe to table deltas
  subscribeDeltas(contract: string, table: string, callback: (data: any) => void): void {
    if (!this.ws) throw new Error('Not connected');

    this.ws.send(JSON.stringify({
      type: 'delta_stream',
      req_id: `${contract}:${table}`,
      data: {
        code: contract,
        table,
        start_from: 'head'
      }
    }));

    this.ws.on('message', (data: string) => {
      const message: StreamMessage = JSON.parse(data);
      if (message.type === 'delta') {
        callback(message.content);
      }
    });
  }

  private reconnect(): void {
    setTimeout(() => {
      console.log('Reconnecting...');
      this.connect();
    }, 5000);
  }

  disconnect(): void {
    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }
  }
}

// Usage
const stream = new HyperionStream();
await stream.connect();

// Listen for all transfers
stream.subscribeActions('eosio.token', 'transfer', (action) => {
  console.log('Transfer:', action.data);
  // { from: 'alice', to: 'bob', quantity: '100.0000 XPR', memo: 'Payment' }
});

// Listen for NFT mints
stream.subscribeActions('atomicassets', 'mintasset', (action) => {
  console.log('NFT minted:', action.data);
});
```

### Stream Table Deltas

Monitor table changes in real-time:

```typescript
// Watch for user profile changes
stream.subscribeDeltas('eosio.proton', 'usersinfo', (delta) => {
  if (delta.present) {
    console.log('Profile updated:', delta.data);
  } else {
    console.log('Profile removed:', delta.primary_key);
  }
});

// Watch for oracle price updates
stream.subscribeDeltas('oracles', 'data', (delta) => {
  console.log('Price updated:', delta.data);
});
```

---

## Polling Pattern

For simpler integrations, poll the Hyperion API:

### Poll for New Actions

```typescript
class ActionPoller {
  private lastTimestamp: string = '';
  private pollInterval: number;
  private running: boolean = false;

  constructor(
    private account: string,
    private filter: string | undefined,
    intervalMs: number = 5000
  ) {
    this.pollInterval = intervalMs;
    this.lastTimestamp = new Date().toISOString();
  }

  start(callback: (actions: any[]) => void): void {
    this.running = true;
    this.poll(callback);
  }

  stop(): void {
    this.running = false;
  }

  private async poll(callback: (actions: any[]) => void): Promise<void> {
    while (this.running) {
      try {
        const url = new URL('https://proton.eosusa.io/v2/history/get_actions');
        url.searchParams.set('account', this.account);
        url.searchParams.set('after', this.lastTimestamp);
        url.searchParams.set('sort', 'asc');
        url.searchParams.set('limit', '100');

        if (this.filter) {
          url.searchParams.set('filter', this.filter);
        }

        const response = await fetch(url);
        const data = await response.json();

        if (data.actions && data.actions.length > 0) {
          callback(data.actions);

          // Update timestamp to latest action
          const lastAction = data.actions[data.actions.length - 1];
          this.lastTimestamp = lastAction['@timestamp'];
        }
      } catch (error) {
        console.error('Polling error:', error);
      }

      await this.sleep(this.pollInterval);
    }
  }

  private sleep(ms: number): Promise<void> {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

// Usage: Poll for incoming transfers
const poller = new ActionPoller('myaccount', 'eosio.token:transfer', 3000);

poller.start((actions) => {
  for (const action of actions) {
    if (action.act.data.to === 'myaccount') {
      console.log('Received payment:', action.act.data);
      // Handle incoming payment
    }
  }
});
```

### Poll for Table Changes

```typescript
class TablePoller<T> {
  private lastData: Map<string, T> = new Map();

  constructor(
    private contract: string,
    private table: string,
    private scope: string = contract,
    private pollInterval: number = 5000
  ) {}

  async start(
    onAdd: (row: T) => void,
    onUpdate: (oldRow: T, newRow: T) => void,
    onRemove: (row: T) => void,
    getKey: (row: T) => string
  ): Promise<void> {
    while (true) {
      try {
        const { rows } = await rpc.get_table_rows({
          code: this.contract,
          scope: this.scope,
          table: this.table,
          limit: 1000
        });

        const currentKeys = new Set<string>();

        for (const row of rows) {
          const key = getKey(row);
          currentKeys.add(key);

          const existing = this.lastData.get(key);
          if (!existing) {
            onAdd(row);
          } else if (JSON.stringify(existing) !== JSON.stringify(row)) {
            onUpdate(existing, row);
          }

          this.lastData.set(key, row);
        }

        // Check for removed rows
        for (const [key, row] of this.lastData) {
          if (!currentKeys.has(key)) {
            onRemove(row);
            this.lastData.delete(key);
          }
        }
      } catch (error) {
        console.error('Table poll error:', error);
      }

      await new Promise(r => setTimeout(r, this.pollInterval));
    }
  }
}

// Usage: Watch challenges table
const challengePoller = new TablePoller('pricebattle', 'challenges');

challengePoller.start(
  (challenge) => console.log('New challenge:', challenge),
  (old, updated) => console.log('Challenge updated:', old.id, '->', updated),
  (challenge) => console.log('Challenge removed:', challenge.id),
  (row) => String(row.id)
);
```

---

## Notification Service Architecture

### Backend Service

Build a notification service that watches the chain and notifies users:

```typescript
import WebSocket from 'ws';
import { Server } from 'socket.io';

interface Subscription {
  userId: string;
  account: string;
  filters: string[];
}

class NotificationService {
  private hyperion: HyperionStream;
  private io: Server;
  private subscriptions: Map<string, Subscription[]> = new Map();

  constructor(ioServer: Server) {
    this.io = ioServer;
    this.hyperion = new HyperionStream();
  }

  async start(): Promise<void> {
    await this.hyperion.connect();

    // Subscribe to common actions
    this.watchTransfers();
    this.watchNFTs();
  }

  private watchTransfers(): void {
    this.hyperion.subscribeActions('eosio.token', 'transfer', (action) => {
      const { from, to, quantity, memo } = action.data;

      // Notify recipient
      this.notifyAccount(to, {
        type: 'transfer_received',
        from,
        quantity,
        memo,
        txId: action.trx_id
      });

      // Notify sender
      this.notifyAccount(from, {
        type: 'transfer_sent',
        to,
        quantity,
        memo,
        txId: action.trx_id
      });
    });
  }

  private watchNFTs(): void {
    this.hyperion.subscribeActions('atomicassets', 'transfer', (action) => {
      const { from, to, asset_ids } = action.data;

      this.notifyAccount(to, {
        type: 'nft_received',
        from,
        assetIds: asset_ids,
        txId: action.trx_id
      });
    });
  }

  private notifyAccount(account: string, notification: any): void {
    // Emit to all connected clients watching this account
    this.io.to(`account:${account}`).emit('notification', notification);

    // Could also store in database, send push notification, etc.
  }

  // Called when user connects
  subscribeUser(socketId: string, account: string): void {
    this.io.sockets.sockets.get(socketId)?.join(`account:${account}`);
  }
}

// Express + Socket.io setup
import express from 'express';
import { createServer } from 'http';
import { Server } from 'socket.io';

const app = express();
const httpServer = createServer(app);
const io = new Server(httpServer, { cors: { origin: '*' } });

const notificationService = new NotificationService(io);

io.on('connection', (socket) => {
  console.log('Client connected:', socket.id);

  socket.on('subscribe', (account: string) => {
    notificationService.subscribeUser(socket.id, account);
    console.log(`${socket.id} subscribed to ${account}`);
  });
});

notificationService.start();
httpServer.listen(3001);
```

### Frontend Client

```typescript
import { io, Socket } from 'socket.io-client';

class NotificationClient {
  private socket: Socket;
  private handlers: Map<string, ((data: any) => void)[]> = new Map();

  constructor(serverUrl: string) {
    this.socket = io(serverUrl);

    this.socket.on('notification', (notification) => {
      const handlers = this.handlers.get(notification.type) || [];
      handlers.forEach(handler => handler(notification));

      // Also call 'all' handlers
      const allHandlers = this.handlers.get('all') || [];
      allHandlers.forEach(handler => handler(notification));
    });
  }

  subscribe(account: string): void {
    this.socket.emit('subscribe', account);
  }

  on(type: string, handler: (data: any) => void): void {
    const handlers = this.handlers.get(type) || [];
    handlers.push(handler);
    this.handlers.set(type, handlers);
  }
}

// React hook
import { useEffect, useState } from 'react';

export function useNotifications(account: string) {
  const [notifications, setNotifications] = useState<any[]>([]);
  const [client] = useState(() => new NotificationClient('http://localhost:3001'));

  useEffect(() => {
    if (!account) return;

    client.subscribe(account);

    client.on('all', (notification) => {
      setNotifications(prev => [notification, ...prev].slice(0, 50));
    });
  }, [account]);

  return notifications;
}

// Usage in component
function NotificationBell({ account }) {
  const notifications = useNotifications(account);

  return (
    <div>
      {notifications.map((n, i) => (
        <div key={i}>
          {n.type === 'transfer_received' && (
            <span>Received {n.quantity} from {n.from}</span>
          )}
          {n.type === 'nft_received' && (
            <span>Received NFT from {n.from}</span>
          )}
        </div>
      ))}
    </div>
  );
}
```

---

## Transaction Confirmation

Wait for transaction confirmation:

```typescript
interface TxResult {
  transaction_id: string;
  processed: {
    block_num: number;
    block_time: string;
  };
}

async function waitForConfirmation(
  txId: string,
  confirmations: number = 1,
  timeoutMs: number = 30000
): Promise<boolean> {
  const startTime = Date.now();

  while (Date.now() - startTime < timeoutMs) {
    try {
      const response = await fetch(
        `https://proton.eosusa.io/v2/history/get_transaction?id=${txId}`
      );
      const data = await response.json();

      if (data.trx_id) {
        // Transaction found
        const info = await rpc.get_info();
        const txBlockNum = data.actions[0]?.block_num;
        const currentBlock = info.head_block_num;
        const confirmedBlocks = currentBlock - txBlockNum;

        if (confirmedBlocks >= confirmations) {
          return true;
        }
      }
    } catch (error) {
      // Transaction not yet indexed, continue waiting
    }

    await new Promise(r => setTimeout(r, 1000));
  }

  return false;
}

// Usage
const result = await session.transact({ actions }, { broadcast: true });
const confirmed = await waitForConfirmation(result.transaction_id, 3);

if (confirmed) {
  console.log('Transaction confirmed!');
} else {
  console.log('Confirmation timeout');
}
```

---

## Event-Driven Architecture

### Database Sync Pattern

Sync blockchain data to a database for fast queries:

```typescript
import { Pool } from 'pg';

class BlockchainSync {
  private pool: Pool;
  private stream: HyperionStream;

  constructor(dbConfig: any) {
    this.pool = new Pool(dbConfig);
    this.stream = new HyperionStream();
  }

  async start(): Promise<void> {
    await this.stream.connect();

    // Sync transfers
    this.stream.subscribeActions('eosio.token', 'transfer', async (action) => {
      await this.pool.query(
        `INSERT INTO transfers (tx_id, from_account, to_account, quantity, memo, timestamp)
         VALUES ($1, $2, $3, $4, $5, $6)
         ON CONFLICT (tx_id) DO NOTHING`,
        [
          action.trx_id,
          action.data.from,
          action.data.to,
          action.data.quantity,
          action.data.memo,
          action['@timestamp']
        ]
      );
    });

    // Sync challenges
    this.stream.subscribeDeltas('pricebattle', 'challenges', async (delta) => {
      if (delta.present) {
        await this.pool.query(
          `INSERT INTO challenges (id, creator, opponent, amount, status, created_at)
           VALUES ($1, $2, $3, $4, $5, NOW())
           ON CONFLICT (id) DO UPDATE SET
             opponent = $2, status = $4`,
          [delta.data.id, delta.data.creator, delta.data.opponent, delta.data.amount, delta.data.status]
        );
      } else {
        await this.pool.query('DELETE FROM challenges WHERE id = $1', [delta.primary_key]);
      }
    });
  }
}
```

### Webhook Pattern

Send webhooks when events occur:

```typescript
import axios from 'axios';

interface WebhookConfig {
  url: string;
  account: string;
  events: string[];
  secret: string;
}

class WebhookDispatcher {
  private webhooks: WebhookConfig[] = [];

  register(config: WebhookConfig): void {
    this.webhooks.push(config);
  }

  async dispatch(event: string, account: string, payload: any): Promise<void> {
    const matching = this.webhooks.filter(
      w => w.account === account && w.events.includes(event)
    );

    for (const webhook of matching) {
      try {
        const signature = this.sign(payload, webhook.secret);

        await axios.post(webhook.url, {
          event,
          payload,
          timestamp: Date.now()
        }, {
          headers: {
            'X-Webhook-Signature': signature,
            'Content-Type': 'application/json'
          }
        });
      } catch (error) {
        console.error(`Webhook failed: ${webhook.url}`, error);
      }
    }
  }

  private sign(payload: any, secret: string): string {
    const crypto = require('crypto');
    return crypto
      .createHmac('sha256', secret)
      .update(JSON.stringify(payload))
      .digest('hex');
  }
}

// Usage
const dispatcher = new WebhookDispatcher();

dispatcher.register({
  url: 'https://myapp.com/webhooks/payments',
  account: 'merchant',
  events: ['transfer_received'],
  secret: 'my-webhook-secret'
});

// In your stream handler:
stream.subscribeActions('eosio.token', 'transfer', (action) => {
  dispatcher.dispatch('transfer_received', action.data.to, action.data);
});
```

---

## Quick Reference

### Hyperion Stream Events

```typescript
// Action subscription
{
  type: 'action_stream',
  data: { contract: 'eosio.token', action: 'transfer' }
}

// Delta subscription
{
  type: 'delta_stream',
  data: { code: 'pricebattle', table: 'challenges' }
}
```

### Common Filters

| Filter | Description |
|--------|-------------|
| `eosio.token:transfer` | All token transfers |
| `atomicassets:*` | All NFT actions |
| `pricebattle:*` | All PriceBattle actions |
| `eosio:newaccount` | New account creation |

### Polling Intervals

| Use Case | Recommended Interval |
|----------|---------------------|
| Real-time UI | 1-3 seconds |
| Background sync | 5-10 seconds |
| Analytics | 30-60 seconds |

### Performance Tips

1. **Use streaming over polling** when possible
2. **Filter server-side** - don't fetch everything and filter client-side
3. **Implement reconnection logic** for WebSocket connections
4. **Use database indexes** for synced blockchain data
5. **Batch notifications** to avoid overwhelming users

---

## Libraries

### block-stream

TypeScript library for real-time XPR Network streaming via State History Plugin.

**Repository:** https://github.com/SuperstrongBE/block-stream

**Features:**
- WebSocket streaming with automatic ABI decoding
- Microservice architecture with chainable processors
- Contract whitelisting and granular filtering
- Winston logging with configurable levels

**Installation:**
```bash
npm install @aspect/block-stream
# or
bun install @aspect/block-stream
```

**Example:**
```typescript
import { BlockStreamClient } from '@aspect/block-stream';

const client = new BlockStreamClient({
  socketAddress: 'ws://proton-ship.eosusa.io:8080',
  contracts: {
    'eosio.token': {
      tables: ['accounts'],
      actions: ['transfer']
    },
    'pricebattle': {
      tables: ['*'],      // All tables
      actions: ['*']      // All actions
    }
  }
});

client
  .pipe(async (ctx) => {
    if (ctx.$action) {
      console.log('Action:', ctx.$action.name, ctx.$action.data);
    }
    if (ctx.$delta) {
      console.log('Delta:', ctx.$table, ctx.$delta);
    }
  })
  .start();
```

**Best for:** Production indexers, analytics pipelines, real-time dashboards requiring direct State History access.
