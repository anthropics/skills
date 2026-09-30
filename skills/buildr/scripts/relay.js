#!/usr/bin/env node
/**
 * Buildr Relay - Always-on Telegram relay daemon for Claude Code
 *
 * Run via PM2: pm2 start relay.js --name buildr-relay
 *
 * Responsibilities:
 * 1. Poll Telegram for messages → write to inbox file
 * 2. Watch outbox file → send to Telegram
 * 3. Monitor CC heartbeat → detect offline, fallback to claude -p
 * 4. Handle STOP, permissions, typing indicators
 * 5. Slash commands: /status /help /clear /reconnect
 */

const https = require('https');
const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// --- Load config ---
const HOME = process.env.BUILDR_HOME || path.join(process.env.HOME || '/root', '.buildr');
const CONFIG_FILE = path.join(HOME, 'config.env');

function loadConfig() {
  const cfg = {};
  try {
    const lines = fs.readFileSync(CONFIG_FILE, 'utf8').split('\n');
    for (const line of lines) {
      const match = line.match(/^([A-Z_]+)=(.+)$/);
      if (match) cfg[match[1]] = match[2].trim().replace(/^['"]|['"]$/g, '');
    }
  } catch (err) {
    console.error(`[relay] Cannot read config: ${CONFIG_FILE}`);
    console.error('[relay] Run setup.sh first.');
    process.exit(1);
  }
  return cfg;
}

const config = loadConfig();
const TOKEN = config.BOT_TOKEN;
const USER_ID = config.USER_ID;

if (!TOKEN || !USER_ID) {
  console.error('[relay] BOT_TOKEN and USER_ID must be set in config.env');
  process.exit(1);
}

// --- File paths ---
const INBOX       = path.join(HOME, 'inbox.jsonl');
const OUTBOX      = path.join(HOME, 'outbox.jsonl');
const OFFSET_FILE = path.join(HOME, 'poll-offset');
const HEARTBEAT   = path.join(HOME, 'heartbeat');
const ALIVE_FILE  = path.join(HOME, 'cc-alive');
const STOP_FLAG   = path.join(HOME, 'stop-flag');
const PERM_REQID  = path.join(HOME, 'perm-reqid');
const PERM_RESP   = path.join(HOME, 'perm-response');

// --- Settings ---
const HEARTBEAT_TIMEOUT = 5 * 60 * 1000; // 5 min = CC considered dead
const OUTBOX_INTERVAL   = 2000;           // check outbox every 2s
const HEARTBEAT_CHECK   = 30000;          // check heartbeat every 30s

// --- State ---
let pollOffset = 0;
try { pollOffset = parseInt(fs.readFileSync(OFFSET_FILE, 'utf8').trim()) || 0; } catch {}
const seenIds = new Set();
let ccAlive = false;
let lastDeadNotify = 0;
let offlineBusy = false;

// --- Telegram API ---
function tg(method, body) {
  return new Promise((resolve, reject) => {
    const payload = JSON.stringify(body || {});
    const req = https.request({
      hostname: 'api.telegram.org',
      path: `/bot${TOKEN}/${method}`,
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(payload) },
      timeout: 40000,
    }, res => {
      let data = '';
      res.on('data', c => data += c);
      res.on('end', () => {
        try { resolve(JSON.parse(data)); } catch { resolve({ ok: false }); }
      });
    });
    req.on('error', reject);
    req.on('timeout', () => { req.destroy(); reject(new Error('timeout')); });
    req.write(payload);
    req.end();
  });
}

async function send(text) {
  try {
    // Split long messages (TG limit 4096)
    const chunks = [];
    let remaining = text;
    while (remaining.length > 0) {
      chunks.push(remaining.slice(0, 4000));
      remaining = remaining.slice(4000);
    }
    for (const chunk of chunks) {
      await tg('sendMessage', { chat_id: USER_ID, text: chunk });
    }
  } catch (err) {
    console.error(`[relay] send error: ${err.message}`);
  }
}

function typing() {
  return tg('sendChatAction', { chat_id: USER_ID, action: 'typing' }).catch(() => {});
}

// --- Helpers ---
function readFile(p) {
  try { return fs.readFileSync(p, 'utf8').trim(); } catch { return null; }
}

function countUnread() {
  try {
    const lastRead = parseInt(readFile(path.join(HOME, 'last-read')) || '0');
    const lines = fs.readFileSync(INBOX, 'utf8').trim().split('\n').filter(Boolean);
    return lines.filter(l => {
      try { return JSON.parse(l).update_id > lastRead; } catch { return false; }
    }).length;
  } catch { return 0; }
}

// --- Telegram Polling ---
async function poll() {
  while (true) {
    try {
      const res = await tg('getUpdates', { offset: pollOffset, timeout: 30, limit: 10 });
      if (!res.ok || !res.result || res.result.length === 0) continue;

      for (const update of res.result) {
        pollOffset = update.update_id + 1;
        fs.writeFileSync(OFFSET_FILE, String(pollOffset));

        const msg = update.message;
        if (!msg || !msg.text) continue;
        if (String(msg.from?.id || '') !== USER_ID) continue;

        const uid = String(update.update_id);
        if (seenIds.has(uid)) continue;
        seenIds.add(uid);

        // Write to inbox
        const entry = {
          ts: Date.now() / 1000,
          update_id: update.update_id,
          chat_id: String(msg.chat.id),
          text: msg.text,
          from: msg.from.first_name || 'User',
        };
        fs.appendFileSync(INBOX, JSON.stringify(entry) + '\n');
        console.log(`[relay] ${new Date().toISOString()} | in: ${msg.text.slice(0, 80)}`);

        const textLower = msg.text.trim().toLowerCase();

        // Typing indicator when CC is alive
        if (ccAlive && textLower !== 'stop' && !msg.text.startsWith('/')) {
          typing();
        }

        // Permission response handling
        if (fs.existsSync(PERM_REQID) && !fs.existsSync(PERM_RESP)) {
          const reqId = readFile(PERM_REQID);
          if (reqId) {
            fs.writeFileSync(PERM_RESP, `${reqId}\n${msg.text.trim()}`);
            if (textLower === 'yes' || textLower === 'y') {
              console.log(`[relay] Permission APPROVED`);
              await send('Permission APPROVED.');
            } else if (textLower === 'no' || textLower === 'n') {
              console.log(`[relay] Permission DENIED`);
              await send('Permission DENIED.');
            } else {
              console.log(`[relay] Permission: custom response`);
              await send('Custom response sent to CC.');
            }
            try { fs.unlinkSync(PERM_REQID); } catch {}
          }
        }

        // STOP command
        if (textLower === 'stop') {
          fs.writeFileSync(STOP_FLAG, String(Date.now()));
          console.log('[relay] STOP flag set');
          await send('STOP received. CC will halt on next action.');
          continue;
        }

        // Clear STOP on any non-stop, non-perm message
        if (fs.existsSync(STOP_FLAG) && !['yes', 'y', 'no', 'n'].includes(textLower)) {
          try { fs.unlinkSync(STOP_FLAG); } catch {}
          console.log('[relay] STOP cleared (new message)');
        }

        // Slash commands
        if (msg.text.startsWith('/')) {
          await handleCommand(msg.text);
          continue;
        }

        // Offline fallback
        if (!ccAlive && !fs.existsSync(PERM_REQID) &&
            !['yes', 'y', 'no', 'n', 'stop'].includes(textLower)) {
          offlineReply(msg.text);
        }
      }
    } catch (err) {
      console.error(`[relay] poll error: ${err.message}`);
      await new Promise(r => setTimeout(r, 3000));
    }
  }
}

// --- Commands ---
async function handleCommand(text) {
  const cmd = text.split(' ')[0].toLowerCase();
  switch (cmd) {
    case '/status': {
      const age = heartbeatAge();
      const hbStr = age === Infinity ? 'never' : `${Math.round(age / 1000)}s ago`;
      const mode = ccAlive ? 'ONLINE (full session)' : 'OFFLINE (claude -p fallback)';
      await send(`Buildr Status\n\nCC: ${ccAlive ? 'ALIVE' : 'DOWN'} (heartbeat: ${hbStr})\nMode: ${mode}\nUnread: ${countUnread()}`);
      break;
    }
    case '/clear':
      fs.writeFileSync(INBOX, '');
      await send('Inbox cleared.');
      break;
    case '/help':
      await send(
        'Buildr Commands\n\n' +
        '/status - Check CC session status\n' +
        '/clear - Clear message inbox\n' +
        '/help - Show this help\n' +
        'STOP - Halt CC immediately\n\n' +
        'Online: messages handled by CC hooks\n' +
        'Offline: messages processed via claude -p'
      );
      break;
    case '/reconnect':
      await send('CC needs VS Code to reconnect for full session.\nOffline messages are processed with claude -p in the meantime.');
      break;
  }
}

// --- Heartbeat Monitor ---
function heartbeatAge() {
  try {
    return Date.now() - parseInt(fs.readFileSync(HEARTBEAT, 'utf8').trim());
  } catch {
    return Infinity;
  }
}

function checkHeartbeat() {
  const age = heartbeatAge();
  const wasAlive = ccAlive;
  ccAlive = age < HEARTBEAT_TIMEOUT;
  fs.writeFileSync(ALIVE_FILE, ccAlive ? '1' : '0');

  if (wasAlive && !ccAlive) {
    console.log(`[relay] CC went OFFLINE (heartbeat: ${Math.round(age / 1000)}s)`);
    const now = Date.now();
    if (now - lastDeadNotify > 60000) {
      lastDeadNotify = now;
      send(
        'CC session went offline.\n\n' +
        'Send messages here - I\'ll process them with claude -p.\n' +
        'Full session resumes when VS Code reconnects.'
      );
    }
  } else if (!wasAlive && ccAlive) {
    console.log('[relay] CC is back ONLINE');
    send('CC session is back online!');
  }
}

// --- Outbox Watcher ---
async function checkOutbox() {
  try {
    if (!fs.existsSync(OUTBOX)) return;
    const content = fs.readFileSync(OUTBOX, 'utf8').trim();
    if (!content) return;
    fs.writeFileSync(OUTBOX, ''); // clear immediately
    const lines = content.split('\n').filter(Boolean);
    for (const line of lines) {
      try {
        const msg = JSON.parse(line);
        await typing();
        await new Promise(r => setTimeout(r, 500));
        await send(msg.text);
        console.log(`[relay] ${new Date().toISOString()} | out: ${msg.text.slice(0, 80)}`);
      } catch (err) {
        console.error(`[relay] outbox parse error: ${err.message}`);
      }
    }
  } catch (err) {
    if (err.code !== 'ENOENT') console.error(`[relay] outbox error: ${err.message}`);
  }
}

// --- Offline Fallback (claude -p) ---
async function offlineReply(text) {
  if (offlineBusy) return;
  offlineBusy = true;
  try {
    await typing();
    const prompt = `You are responding via Telegram. The user's Claude Code session is offline. ` +
      `The user sent: "${text.replace(/"/g, '\\"')}"\n\n` +
      `Respond helpfully and concisely. Complex tasks should wait for the full CC session.`;
    const result = execSync(
      `claude -p "${prompt.replace(/"/g, '\\"')}" --max-turns 1 2>/dev/null`,
      { timeout: 120000, encoding: 'utf8', cwd: process.env.HOME || '/root' }
    );
    if (result && result.trim()) {
      await send(result.trim().slice(0, 4000));
    } else {
      await send('Message received. Full processing resumes when VS Code reconnects.');
    }
  } catch (err) {
    console.error(`[relay] offline error: ${err.message}`);
    await send('Got your message. Saved for when full session resumes.');
  } finally {
    offlineBusy = false;
  }
}

// --- Intervals ---
setInterval(checkOutbox, OUTBOX_INTERVAL);
setInterval(checkHeartbeat, HEARTBEAT_CHECK);
setInterval(() => { if (seenIds.size > 1000) seenIds.clear(); }, 3600000);

// Auto-cleanup stale permission files (prevents message interception)
setInterval(() => {
  try {
    if (fs.existsSync(PERM_REQID)) {
      const age = Date.now() - fs.statSync(PERM_REQID).mtimeMs;
      if (age > 120000) { // 2 min = stale
        fs.unlinkSync(PERM_REQID);
        try { fs.unlinkSync(PERM_RESP); } catch {}
        console.log('[relay] Cleaned stale permission files');
      }
    }
  } catch {}
}, 30000);

// --- Start ---
console.log(`[relay] Buildr Relay starting`);
console.log(`[relay] Home: ${HOME}`);
console.log(`[relay] User: ${USER_ID}`);
console.log(`[relay] Heartbeat timeout: ${HEARTBEAT_TIMEOUT / 1000}s`);

checkHeartbeat();
poll();
