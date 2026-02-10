#!/usr/bin/env node
import fs from 'fs';
import path from 'path';

const GROQ_API_KEY = process.env.GROQ_API_KEY;
if (!GROQ_API_KEY) {
  console.error('❌ Please set GROQ_API_KEY environment variable');
  process.exit(1);
}

async function transcribe(audioFilePath) {
  if (!fs.existsSync(audioFilePath)) {
    console.error('❌ File not found:', audioFilePath);
    process.exit(1);
  }

  const fileName = path.basename(audioFilePath);
  const fileBuffer = fs.readFileSync(audioFilePath);

  console.log(`📁 File: ${fileName}`);
  console.log('🔄 Uploading and transcribing...');

  const form = new FormData();
  const blob = new Blob([fileBuffer], { type: 'application/octet-stream' });
  form.append('file', blob, fileName);
  form.append('model', 'whisper-large-v3-turbo');
  form.append('language', 'zh');
  form.append('response_format', 'json');

  const res = await fetch('https://api.groq.com/openai/v1/audio/transcriptions', {
    method: 'POST',
    headers: { Authorization: `Bearer ${GROQ_API_KEY}` },
    body: form,
  });

  if (!res.ok) {
    const err = await res.text();
    console.error('❌ API error:', err);
    process.exit(1);
  }

  const result = await res.json();
  console.log('\n✅ Transcription complete\n');
  console.log(result.text);

  const out = `${path.basename(audioFilePath, path.extname(audioFilePath))}_transcript.txt`;
  fs.writeFileSync(out, result.text, 'utf8');
  console.log('💾 Saved to', out);
}

const file = process.argv[2];
if (!file) {
  console.error('Usage: node scripts/transcribe.mjs <audio-file>');
  process.exit(1);
}

transcribe(file).catch(err => { console.error('❌', err); process.exit(1); });
