// stdin: JSON array of TeX strings -> stdout: JSON array of HTML (display mode)
const katex = require('katex');
let buf = '';
process.stdin.on('data', d => buf += d);
process.stdin.on('end', () => {
  const arr = JSON.parse(buf);
  const out = arr.map(t => katex.renderToString(t, { displayMode: true, throwOnError: false, output: 'html' }));
  process.stdout.write(JSON.stringify(out));
});
