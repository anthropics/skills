import { spawn } from 'node:child_process';
import fs from 'node:fs';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';

const SUPPORTED_IMAGE_EXTS = new Set(['.jpg', '.jpeg', '.png', '.gif', '.webp']);

function printUsage(exitCode = 0): never {
  console.log(`Copy image or HTML to system clipboard

Supports:
  - Image files (jpg, png, gif, webp) - copies as image data
  - HTML content - copies as rich text for paste

Usage:
  # Copy image to clipboard
  npx -y bun copy-to-clipboard.ts image /path/to/image.jpg

  # Copy HTML to clipboard
  npx -y bun copy-to-clipboard.ts html "<p>Hello</p>"

  # Copy HTML from file
  npx -y bun copy-to-clipboard.ts html --file /path/to/content.html
`);
  process.exit(exitCode);
}

function resolvePath(filePath: string): string {
  return path.isAbsolute(filePath) ? filePath : path.resolve(process.cwd(), filePath);
}

function inferImageMimeType(imagePath: string): string {
  const ext = path.extname(imagePath).toLowerCase();
  switch (ext) {
    case '.jpg':
    case '.jpeg':
      return 'image/jpeg';
    case '.png':
      return 'image/png';
    case '.gif':
      return 'image/gif';
    case '.webp':
      return 'image/webp';
    default:
      return 'application/octet-stream';
  }
}

type RunResult = { stdout: string; stderr: string; exitCode: number };

async function runCommand(
  command: string,
  args: string[],
  options?: { input?: string | Buffer; allowNonZeroExit?: boolean },
): Promise<RunResult> {
  return await new Promise<RunResult>((resolve, reject) => {
    const child = spawn(command, args, { stdio: ['pipe', 'pipe', 'pipe'] });
    const stdoutChunks: Buffer[] = [];
    const stderrChunks: Buffer[] = [];

    child.stdout.on('data', (chunk) => stdoutChunks.push(Buffer.from(chunk)));
    child.stderr.on('data', (chunk) => stderrChunks.push(Buffer.from(chunk)));
    child.on('error', reject);
    child.on('close', (code) => {
      resolve({
        stdout: Buffer.concat(stdoutChunks).toString('utf8'),
        stderr: Buffer.concat(stderrChunks).toString('utf8'),
        exitCode: code ?? 0,
      });
    });

    if (options?.input != null) child.stdin.write(options.input);
    child.stdin.end();
  }).then((result) => {
    if (!options?.allowNonZeroExit && result.exitCode !== 0) {
      const details = result.stderr.trim() || result.stdout.trim();
      throw new Error(`Command failed (${command}): exit ${result.exitCode}${details ? `\n${details}` : ''}`);
    }
    return result;
  });
}

async function commandExists(command: string): Promise<boolean> {
  if (process.platform === 'win32') {
    const result = await runCommand('where', [command], { allowNonZeroExit: true });
    return result.exitCode === 0 && result.stdout.trim().length > 0;
  }
  const result = await runCommand('which', [command], { allowNonZeroExit: true });
  return result.exitCode === 0 && result.stdout.trim().length > 0;
}

async function runCommandWithFileStdin(command: string, args: string[], filePath: string): Promise<void> {
  await new Promise<void>((resolve, reject) => {
    const child = spawn(command, args, { stdio: ['pipe', 'pipe', 'pipe'] });
    const stderrChunks: Buffer[] = [];
    const stdoutChunks: Buffer[] = [];

    child.stdout.on('data', (chunk) => stdoutChunks.push(Buffer.from(chunk)));
    child.stderr.on('data', (chunk) => stderrChunks.push(Buffer.from(chunk)));
    child.on('error', reject);
    child.on('close', (code) => {
      const exitCode = code ?? 0;
      if (exitCode !== 0) {
        const details = Buffer.concat(stderrChunks).toString('utf8').trim() || Buffer.concat(stdoutChunks).toString('utf8').trim();
        reject(
          new Error(`Command failed (${command}): exit ${exitCode}${details ? `\n${details}` : ''}`),
        );
        return;
      }
      resolve();
    });

    fs.createReadStream(filePath).on('error', reject).pipe(child.stdin);
  });
}

async function withTempDir<T>(prefix: string, fn: (tempDir: string) => Promise<T>): Promise<T> {
  const tempDir = await mkdtemp(path.join(os.tmpdir(), prefix));
  try {
    return await fn(tempDir);
  } finally {
    await rm(tempDir, { recursive: true, force: true });
  }
}

function getMacSwiftClipboardSource(): string {
  return `import AppKit
import Foundation

func die(_ message: String, _ code: Int32 = 1) -> Never {
  FileHandle.standardError.write(message.data(using: .utf8)!)
  exit(code)
}

if CommandLine.arguments.count < 3 {
  die("Usage: clipboard.swift <image|html> <path>\\n")
}

let mode = CommandLine.arguments[1]
let inputPath = CommandLine.arguments[2]
let pasteboard = NSPasteboard.general
pasteboard.clearContents()

switch mode {
case "image":
  guard let image = NSImage(contentsOfFile: inputPath) else {
    die("Failed to load image: \\(inputPath)\\n")
  }
  if !pasteboard.writeObjects([image]) {
    die("Failed to write image to clipboard\\n")
  }

case "html":
  let url = URL(fileURLWithPath: inputPath)
  let data: Data
  do {
    data = try Data(contentsOf: url)
  } catch {
    die("Failed to read HTML file: \\(inputPath)\\n")
  }

  _ = pasteboard.setData(data, forType: .html)

  let options: [NSAttributedString.DocumentReadingOptionKey: Any] = [
    .documentType: NSAttributedString.DocumentType.html,
    .characterEncoding: String.Encoding.utf8.rawValue
  ]

  if let attr = try? NSAttributedString(data: data, options: options, documentAttributes: nil) {
    pasteboard.setString(attr.string, forType: .string)
    if let rtf = try? attr.data(
      from: NSRange(location: 0, length: attr.length),
      documentAttributes: [.documentType: NSAttributedString.DocumentType.rtf]
    ) {
      _ = pasteboard.setData(rtf, forType: .rtf)
    }
  } else if let html = String(data: data, encoding: .utf8) {
    pasteboard.setString(html, forType: .string)
  }

default:
  die("Unknown mode: \\(mode)\\n")
}
`;
}

async function copyImageMac(imagePath: string): Promise<void> {
  await withTempDir('copy-to-clipboard-', async (tempDir) => {
    const swiftPath = path.join(tempDir, 'clipboard.swift');
    await writeFile(swiftPath, getMacSwiftClipboardSource(), 'utf8');
    await runCommand('swift', [swiftPath, 'image', imagePath]);
  });
}

async function copyHtmlMac(htmlFilePath: string): Promise<void> {
  await withTempDir('copy-to-clipboard-', async (tempDir) => {
    const swiftPath = path.join(tempDir, 'clipboard.swift');
    await writeFile(swiftPath, getMacSwiftClipboardSource(), 'utf8');
    await runCommand('swift', [swiftPath, 'html', htmlFilePath]);
  });
}

async function copyImageLinux(imagePath: string): Promise<void> {
  const mime = inferImageMimeType(imagePath);
  if (await commandExists('wl-copy')) {
    await runCommandWithFileStdin('wl-copy', ['--type', mime], imagePath);
    return;
  }
  if (await commandExists('xclip')) {
    await runCommand('xclip', ['-selection', 'clipboard', '-t', mime, '-i', imagePath]);
    return;
  }
  throw new Error('No clipboard tool found. Install `wl-clipboard` (wl-copy) or `xclip`.');
}

async function copyHtmlLinux(htmlFilePath: string): Promise<void> {
  if (await commandExists('wl-copy')) {
    await runCommandWithFileStdin('wl-copy', ['--type', 'text/html'], htmlFilePath);
    return;
  }
  if (await commandExists('xclip')) {
    await runCommand('xclip', ['-selection', 'clipboard', '-t', 'text/html', '-i', htmlFilePath]);
    return;
  }
  throw new Error('No clipboard tool found. Install `wl-clipboard` (wl-copy) or `xclip`.');
}

async function copyImageWindows(imagePath: string): Promise<void> {
  const escaped = imagePath.replace(/'/g, "''");
  const ps = [
    'Add-Type -AssemblyName System.Windows.Forms',
    'Add-Type -AssemblyName System.Drawing',
    `$img = [System.Drawing.Image]::FromFile('${escaped}')`,
    '[System.Windows.Forms.Clipboard]::SetImage($img)',
    '$img.Dispose()',
  ].join('; ');
  await runCommand('powershell.exe', ['-NoProfile', '-Sta', '-Command', ps]);
}

async function copyHtmlWindows(htmlFilePath: string): Promise<void> {
  const escaped = htmlFilePath.replace(/'/g, "''");
  const ps = [
    'Add-Type -AssemblyName System.Windows.Forms',
    `$html = Get-Content -Raw -LiteralPath '${escaped}'`,
    '[System.Windows.Forms.Clipboard]::SetText($html, [System.Windows.Forms.TextDataFormat]::Html)',
  ].join('; ');
  await runCommand('powershell.exe', ['-NoProfile', '-Sta', '-Command', ps]);
}

async function copyImageToClipboard(imagePathInput: string): Promise<void> {
  const imagePath = resolvePath(imagePathInput);
  const ext = path.extname(imagePath).toLowerCase();
  if (!SUPPORTED_IMAGE_EXTS.has(ext)) {
    throw new Error(
      `Unsupported image type: ${ext || '(none)'} (supported: ${Array.from(SUPPORTED_IMAGE_EXTS).join(', ')})`,
    );
  }
  if (!fs.existsSync(imagePath)) throw new Error(`File not found: ${imagePath}`);

  switch (process.platform) {
    case 'darwin':
      await copyImageMac(imagePath);
      return;
    case 'linux':
      await copyImageLinux(imagePath);
      return;
    case 'win32':
      await copyImageWindows(imagePath);
      return;
    default:
      throw new Error(`Unsupported platform: ${process.platform}`);
  }
}

async function copyHtmlFileToClipboard(htmlFilePathInput: string): Promise<void> {
  const htmlFilePath = resolvePath(htmlFilePathInput);
  if (!fs.existsSync(htmlFilePath)) throw new Error(`File not found: ${htmlFilePath}`);

  switch (process.platform) {
    case 'darwin':
      await copyHtmlMac(htmlFilePath);
      return;
    case 'linux':
      await copyHtmlLinux(htmlFilePath);
      return;
    case 'win32':
      await copyHtmlWindows(htmlFilePath);
      return;
    default:
      throw new Error(`Unsupported platform: ${process.platform}`);
  }
}

async function readStdinText(): Promise<string | null> {
  if (process.stdin.isTTY) return null;
  const chunks: Buffer[] = [];
  for await (const chunk of process.stdin) {
    chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
  }
  const text = Buffer.concat(chunks).toString('utf8');
  return text.length > 0 ? text : null;
}

async function copyHtmlToClipboard(args: string[]): Promise<void> {
  let htmlFile: string | undefined;
  const positional: string[] = [];

  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i] ?? '';
    if (arg === '--help' || arg === '-h') printUsage(0);
    if (arg === '--file') {
      htmlFile = args[i + 1];
      i += 1;
      continue;
    }
    if (arg.startsWith('--file=')) {
      htmlFile = arg.slice('--file='.length);
      continue;
    }
    if (arg === '--') {
      positional.push(...args.slice(i + 1));
      break;
    }
    if (arg.startsWith('-')) {
      throw new Error(`Unknown option: ${arg}`);
    }
    positional.push(arg);
  }

  if (htmlFile && positional.length > 0) {
    throw new Error('Do not pass HTML text when using --file.');
  }

  if (htmlFile) {
    await copyHtmlFileToClipboard(htmlFile);
    return;
  }

  const htmlFromArgs = positional.join(' ').trim();
  const htmlFromStdin = (await readStdinText())?.trim() ?? '';
  const html = htmlFromArgs || htmlFromStdin;
  if (!html) throw new Error('Missing HTML input. Provide a string or use --file.');

  await withTempDir('copy-to-clipboard-', async (tempDir) => {
    const htmlPath = path.join(tempDir, 'input.html');
    await writeFile(htmlPath, html, 'utf8');
    await copyHtmlFileToClipboard(htmlPath);
  });
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2);
  if (argv.length === 0) printUsage(1);

  const command = argv[0];
  if (command === '--help' || command === '-h') printUsage(0);

  if (command === 'image') {
    const imagePath = argv[1];
    if (!imagePath) throw new Error('Missing image path.');
    await copyImageToClipboard(imagePath);
    return;
  }

  if (command === 'html') {
    await copyHtmlToClipboard(argv.slice(1));
    return;
  }

  throw new Error(`Unknown command: ${command}`);
}

await main().catch((err) => {
  const message = err instanceof Error ? err.message : String(err);
  console.error(`Error: ${message}`);
  process.exit(1);
});

