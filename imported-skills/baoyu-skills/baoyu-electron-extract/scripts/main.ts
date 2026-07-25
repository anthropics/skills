#!/usr/bin/env bun
import {
  cpSync,
  existsSync,
  mkdirSync,
  readdirSync,
  readFileSync,
  statSync,
  writeFileSync,
} from "fs";
import {
  basename,
  dirname,
  extname,
  isAbsolute,
  join,
  posix as posixPath,
  relative,
  resolve,
  sep,
} from "path";
import { createHash } from "crypto";
import { spawn, spawnSync } from "child_process";
import { homedir } from "os";
import { pathToFileURL } from "url";

interface Options {
  app: string;
  output?: string;
  asar?: string;
  force: boolean;
  skipFormat: boolean;
  skipRestore: boolean;
  noUnpacked: boolean;
  dryRun: boolean;
  json: boolean;
}

interface ResolvedApp {
  appName: string;
  asarPath: string;
  unpackedDir: string | null;
  installRoot: string | null;
}

interface Counts {
  extractedFiles: number;
  restoredFiles: number;
  formattedFiles: number;
  skippedNodeModules: number;
  unpackedFiles: number;
}

interface Report {
  appName: string;
  source: {
    input: string;
    asar: string;
    platform: string;
    installRoot: string | null;
  };
  output: {
    root: string;
    extracted: string;
    unpacked: string | null;
    restored: string | null;
  };
  counts: Counts;
  warnings: string[];
  durationMs: number;
}

function usage(): string {
  return `Usage: main.ts <app> [options]

Extract resources & JavaScript from an installed Electron app.

Arguments:
  <app>              App name (e.g. "Codex", "Visual Studio Code") or absolute
                     path to a .app bundle, install directory, or .asar file.

Options:
  -o, --output PATH  Output directory (default: ~/Downloads/<App>-electron-extract)
      --asar PATH    Override the resolved .asar path
  -f, --force        Allow writing into a non-empty existing output dir
      --skip-format  Skip Prettier formatting (extract only)
      --skip-restore Skip source-map restoration
      --no-unpacked  Don't copy app.asar.unpacked/ alongside
      --dry-run      Print resolved paths and exit without writing
      --json         Emit a single JSON line summary to stdout
  -h, --help         Show this help
`;
}

function fail(message: string, json: boolean): never {
  if (json) {
    process.stdout.write(
      JSON.stringify({ status: "error", error: message }) + "\n"
    );
  } else {
    process.stderr.write(`Error: ${message}\n`);
  }
  process.exit(1);
}

function parseArgs(argv: string[]): Options {
  const opts: Options = {
    app: "",
    force: false,
    skipFormat: false,
    skipRestore: false,
    noUnpacked: false,
    dryRun: false,
    json: false,
  };
  const positional: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "-h" || a === "--help") {
      process.stdout.write(usage());
      process.exit(0);
    } else if (a === "-o" || a === "--output") {
      opts.output = argv[++i];
    } else if (a === "--asar") {
      opts.asar = argv[++i];
    } else if (a === "-f" || a === "--force") {
      opts.force = true;
    } else if (a === "--skip-format") {
      opts.skipFormat = true;
    } else if (a === "--skip-restore") {
      opts.skipRestore = true;
    } else if (a === "--no-unpacked") {
      opts.noUnpacked = true;
    } else if (a === "--dry-run") {
      opts.dryRun = true;
    } else if (a === "--json") {
      opts.json = true;
    } else if (a.startsWith("-")) {
      throw new Error(`unknown option: ${a}\n\n${usage()}`);
    } else {
      positional.push(a);
    }
  }
  if (positional.length === 0 && !opts.asar) {
    throw new Error(
      `missing <app> argument (or pass --asar PATH)\n\n${usage()}`
    );
  }
  if (positional.length > 1) {
    throw new Error(
      `too many positional arguments: ${positional.join(", ")}\n\n${usage()}`
    );
  }
  opts.app = positional[0] ?? "";
  return opts;
}

function sanitizeAppName(name: string): string {
  return name.replace(/[\\/:*?"<>|]/g, "_").replace(/\s+/g, "-");
}

function appNameFromPath(p: string): string {
  const parts = resolve(p).split(sep);
  for (let i = parts.length - 1; i >= 0; i--) {
    if (parts[i].endsWith(".app")) return parts[i].slice(0, -4);
  }
  const n = basename(p);
  if (n === "app.asar") {
    if (
      parts.length >= 3 &&
      parts[parts.length - 2].toLowerCase() === "resources"
    ) {
      return parts[parts.length - 3];
    }
    if (parts.length >= 2) return parts[parts.length - 2];
  }
  if (n.endsWith(".asar")) return n.slice(0, -5);
  if (n.endsWith(".app")) return n.slice(0, -4);
  return n;
}

function existsAsFile(p: string): boolean {
  try {
    return statSync(p).isFile();
  } catch {
    return false;
  }
}

function existsAsDir(p: string): boolean {
  try {
    return statSync(p).isDirectory();
  } catch {
    return false;
  }
}

function findAsarUnderDir(dir: string): string | null {
  const candidates = [
    join(dir, "resources", "app.asar"),
    join(dir, "Resources", "app.asar"),
    join(dir, "app.asar"),
  ];
  for (const c of candidates) {
    if (existsAsFile(c)) return c;
  }
  if (!existsAsDir(dir)) return null;
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    if (!entry.isDirectory()) continue;
    const nested = join(dir, entry.name, "resources", "app.asar");
    if (existsAsFile(nested)) return nested;
  }
  return null;
}

function resolveByPath(input: string): ResolvedApp | null {
  if (!existsSync(input)) return null;
  const st = statSync(input);
  if (st.isFile() && input.endsWith(".asar")) {
    return {
      appName: appNameFromPath(input),
      asarPath: input,
      unpackedDir: existsAsDir(input + ".unpacked")
        ? input + ".unpacked"
        : null,
      installRoot: dirname(input),
    };
  }
  if (st.isDirectory()) {
    if (input.endsWith(".app")) {
      const asar = join(input, "Contents", "Resources", "app.asar");
      if (existsAsFile(asar)) {
        return {
          appName: appNameFromPath(input),
          asarPath: asar,
          unpackedDir: existsAsDir(asar + ".unpacked")
            ? asar + ".unpacked"
            : null,
          installRoot: input,
        };
      }
      return null;
    }
    const asar = findAsarUnderDir(input);
    if (asar) {
      return {
        appName: appNameFromPath(input),
        asarPath: asar,
        unpackedDir: existsAsDir(asar + ".unpacked")
          ? asar + ".unpacked"
          : null,
        installRoot: input,
      };
    }
  }
  return null;
}

function listAppCandidates(name: string): string[] {
  const lower = name.toLowerCase();
  const stripped = lower.endsWith(".app") ? lower.slice(0, -4) : lower;
  const matches: string[] = [];

  if (process.platform === "darwin") {
    const roots = ["/Applications", join(homedir(), "Applications")];
    for (const root of roots) {
      if (!existsAsDir(root)) continue;
      for (const entry of readdirSync(root, { withFileTypes: true })) {
        if (!entry.isDirectory()) continue;
        const en = entry.name.toLowerCase();
        const enStripped = en.endsWith(".app") ? en.slice(0, -4) : en;
        if (
          en === lower ||
          en === `${stripped}.app` ||
          enStripped === stripped
        ) {
          matches.push(join(root, entry.name));
        }
      }
    }
  } else if (process.platform === "win32") {
    const roots = [
      process.env.LOCALAPPDATA
        ? join(process.env.LOCALAPPDATA, "Programs")
        : null,
      process.env.PROGRAMFILES || null,
      process.env["PROGRAMFILES(X86)"] || null,
      process.env.APPDATA || null,
    ].filter((x): x is string => Boolean(x));
    for (const root of roots) {
      if (!existsAsDir(root)) continue;
      for (const entry of readdirSync(root, { withFileTypes: true })) {
        if (!entry.isDirectory()) continue;
        if (entry.name.toLowerCase() === stripped) {
          matches.push(join(root, entry.name));
        }
      }
    }
  }
  return matches;
}

function resolveApp(input: string): ResolvedApp {
  if (isAbsolute(input)) {
    const r = resolveByPath(input);
    if (r) return r;
    throw new Error(`path exists but no app.asar found at or under: ${input}`);
  }

  if (process.platform !== "darwin" && process.platform !== "win32") {
    throw new Error(
      `platform ${process.platform} is not auto-supported. Pass --asar /path/to/app.asar to override.`
    );
  }

  const candidates = listAppCandidates(input);
  if (candidates.length === 0) {
    throw new Error(
      `could not find an installed app matching "${input}". Try passing an absolute path or --asar.`
    );
  }

  const resolved = candidates
    .map((c) => resolveByPath(c))
    .filter((r): r is ResolvedApp => r !== null);

  if (resolved.length === 0) {
    throw new Error(
      `found app directories for "${input}" but none contained app.asar:\n  ${candidates.join(
        "\n  "
      )}`
    );
  }
  if (resolved.length > 1) {
    throw new Error(
      `multiple apps match "${input}". Re-run with an absolute path:\n  ${resolved
        .map((r) => r.installRoot ?? r.asarPath)
        .join("\n  ")}`
    );
  }
  return resolved[0];
}

function downloadsDir(): string {
  return join(homedir(), "Downloads");
}

function assertSafeOutputDir(outputDir: string, appName: string): void {
  const root =
    process.platform === "win32" ? outputDir.split(sep)[0] + sep : "/";
  const home = resolve(homedir());
  const cwd = resolve(process.cwd());
  const forbidden = [root, home, cwd];
  if (forbidden.includes(outputDir)) {
    throw new Error(`output directory is unsafe to write into: ${outputDir}`);
  }
  const base = basename(outputDir).toLowerCase();
  const tag = sanitizeAppName(appName).toLowerCase();
  if (!base.includes(tag.toLowerCase()) && !base.includes("electron-extract")) {
    throw new Error(
      `output directory basename must contain the app name (or "electron-extract"): ${outputDir}`
    );
  }
}

function dirIsNonEmpty(p: string): boolean {
  try {
    return readdirSync(p).length > 0;
  } catch {
    return false;
  }
}

function runQuiet(
  cmd: string,
  args: string[]
): { code: number; stderr: string; stdout: string } {
  const r = spawnSync(cmd, args, {
    stdio: ["ignore", "pipe", "pipe"],
    encoding: "utf8",
  });
  if (r.error) return { code: 1, stderr: r.error.message, stdout: "" };
  return {
    code: r.status ?? 1,
    stderr: r.stderr ?? "",
    stdout: r.stdout ?? "",
  };
}

function runForwarded(cmd: string, args: string[]): Promise<number> {
  return new Promise((res) => {
    const proc = spawn(cmd, args, { stdio: ["ignore", "inherit", "inherit"] });
    proc.on("close", (code) => res(code ?? 1));
    proc.on("error", () => res(1));
  });
}

async function extractAsar(
  asarPath: string,
  dest: string,
  json: boolean
): Promise<void> {
  mkdirSync(dest, { recursive: true });
  const args = ["-y", "@electron/asar", "extract", asarPath, dest];
  const code = json
    ? await new Promise<number>((res) => {
        const p = spawn("npx", args, { stdio: ["ignore", "ignore", "pipe"] });
        let err = "";
        p.stderr?.on("data", (d) => (err += d.toString()));
        p.on("close", (c) => {
          if ((c ?? 1) !== 0) process.stderr.write(err);
          res(c ?? 1);
        });
        p.on("error", (e) => {
          process.stderr.write(e.message);
          res(1);
        });
      })
    : await runForwarded("npx", args);
  if (code !== 0)
    throw new Error(`@electron/asar extract failed (code ${code})`);
}

type FileKind = "js" | "css" | "other";

function classifyExt(p: string): FileKind {
  const e = extname(p).toLowerCase();
  if (e === ".js" || e === ".mjs" || e === ".cjs") return "js";
  if (e === ".css") return "css";
  return "other";
}

function walk(
  root: string,
  out: { jsFiles: string[]; cssFiles: string[] },
  counts: Counts
): void {
  for (const entry of readdirSync(root, { withFileTypes: true })) {
    if (entry.name === "node_modules") {
      counts.skippedNodeModules += 1;
      continue;
    }
    const full = join(root, entry.name);
    if (entry.isDirectory()) {
      walk(full, out, counts);
    } else if (entry.isFile()) {
      counts.extractedFiles += 1;
      const k = classifyExt(full);
      if (k === "js") out.jsFiles.push(full);
      else if (k === "css") out.cssFiles.push(full);
    }
  }
}

function countFiles(dir: string): number {
  let total = 0;
  if (!existsAsDir(dir)) return 0;
  const stack = [dir];
  while (stack.length) {
    const cur = stack.pop()!;
    for (const entry of readdirSync(cur, { withFileTypes: true })) {
      const full = join(cur, entry.name);
      if (entry.isDirectory()) stack.push(full);
      else if (entry.isFile()) total += 1;
    }
  }
  return total;
}

function toPosix(p: string): string {
  return p.split(sep).join("/");
}

function sourcePathExt(src: string): string {
  return extname(src.split(/[?#]/)[0]) || ".txt";
}

function stripSourceDecorations(src: string): {
  path: string;
  hadProtocol: boolean;
} {
  let s = src.trim();
  let hadProtocol = false;
  if (/^webpack:\/\/\/?/.test(s)) {
    hadProtocol = true;
    s = s.replace(/^webpack:\/\/\/?/, "");
  } else if (/^file:\/\//.test(s)) {
    hadProtocol = true;
    s = s.replace(/^file:\/\//, "");
  } else if (/^[a-zA-Z][a-zA-Z0-9+.-]*:\/\//.test(s)) {
    hadProtocol = true;
    s = s.replace(/^[a-zA-Z][a-zA-Z0-9+.-]*:\/\//, "");
  }
  return { path: s.split(/[?#]/)[0].replace(/\\/g, "/"), hadProtocol };
}

function isSafeRelativePath(p: string): boolean {
  return (
    p !== "" &&
    p !== "." &&
    p !== ".." &&
    !p.startsWith("../") &&
    !p.includes("/../")
  );
}

function fallbackUnknownPath(src: string): string {
  const h = createHash("sha1").update(src).digest("hex").slice(0, 10);
  return posixPath.join("__unknown", `${h}${sourcePathExt(src)}`);
}

function normalizeForOutputPath(p: string): string {
  let s = p.replace(/\\/g, "/").replace(/^[a-zA-Z]:\//, "");
  if (s.startsWith("/")) s = s.replace(/^\/+/, "");
  return posixPath.normalize(s);
}

function sanitizeEscapedSourcePath(
  normalized: string,
  original: string
): string {
  let s = normalized
    .replace(/\\/g, "/")
    .replace(/^[a-zA-Z]:\//, "")
    .replace(/^\/+/, "");
  while (s.startsWith("../")) s = s.slice(3);
  s = posixPath.normalize(s);
  if (!isSafeRelativePath(s)) return fallbackUnknownPath(original);
  return s;
}

function shouldSkipRestoredSource(src: string): boolean {
  const s = src.replace(/\\/g, "/");
  return s.includes("node_modules/") || s.startsWith("webpack/runtime/");
}

function sourceWithRoot(
  src: string,
  sourceRoot: unknown
): { path: string; hadProtocol: boolean } {
  const source = stripSourceDecorations(src);
  if (typeof sourceRoot !== "string" || sourceRoot.trim() === "") return source;

  const root = stripSourceDecorations(sourceRoot);
  const sourceIsAbsolute =
    source.path.startsWith("/") || /^[a-zA-Z]:[\\/]/.test(source.path);
  if (!root.path || source.hadProtocol || sourceIsAbsolute) {
    return {
      path: source.path,
      hadProtocol: source.hadProtocol || root.hadProtocol,
    };
  }
  return {
    path: posixPath.join(root.path.replace(/\\/g, "/"), source.path),
    hadProtocol: source.hadProtocol || root.hadProtocol,
  };
}

export function normalizeSourcePath(
  src: string,
  mapPath: string,
  extractedRoot: string,
  sourceRoot: unknown
): string {
  const source = sourceWithRoot(src, sourceRoot);
  if (!source.path) return "";

  if (
    !source.hadProtocol &&
    (source.path.startsWith("./") || source.path.startsWith("../"))
  ) {
    const mapRelDir = toPosix(relative(extractedRoot, dirname(mapPath))) || ".";
    const relativeToExtracted = posixPath.normalize(
      posixPath.join(mapRelDir, source.path)
    );
    if (isSafeRelativePath(relativeToExtracted)) return relativeToExtracted;
    return sanitizeEscapedSourcePath(relativeToExtracted, src);
  }

  const normalized = normalizeForOutputPath(source.path);
  if (isSafeRelativePath(normalized)) return normalized;
  return sanitizeEscapedSourcePath(normalized, src);
}

function restoredTargetPath(
  restoredRoot: string,
  sourcePath: string
): string | null {
  const target = resolve(restoredRoot, ...sourcePath.split("/"));
  const rel = relative(restoredRoot, target);
  if (rel === "" || rel.startsWith("..") || isAbsolute(rel)) return null;
  return target;
}

interface MapData {
  sources?: unknown;
  sourcesContent?: unknown;
  sourceRoot?: unknown;
}

export function restoreFromMap(
  mapPath: string,
  extractedRoot: string,
  restoredRoot: string,
  warnings: string[]
): number {
  let raw: string;
  try {
    raw = readFileSync(mapPath, "utf8");
  } catch (e: any) {
    warnings.push(`read ${mapPath}: ${e.message}`);
    return 0;
  }
  let data: MapData;
  try {
    data = JSON.parse(raw);
  } catch (e: any) {
    warnings.push(`parse ${mapPath}: ${e.message}`);
    return 0;
  }
  const sources = Array.isArray(data.sources)
    ? (data.sources as unknown[])
    : null;
  const contents = Array.isArray(data.sourcesContent)
    ? (data.sourcesContent as unknown[])
    : null;
  if (!sources || !contents) return 0;
  if (sources.length !== contents.length) {
    warnings.push(`${mapPath}: sources/sourcesContent length mismatch`);
  }
  const n = Math.min(sources.length, contents.length);
  let written = 0;
  for (let i = 0; i < n; i++) {
    const src = sources[i];
    const content = contents[i];
    if (typeof src !== "string" || typeof content !== "string") continue;
    if (shouldSkipRestoredSource(src)) continue;
    const restoredPath = normalizeSourcePath(
      src,
      mapPath,
      extractedRoot,
      data.sourceRoot
    );
    if (!restoredPath) continue;
    const target = restoredTargetPath(restoredRoot, restoredPath);
    if (!target) {
      warnings.push(`${mapPath}: unsafe restored path for source ${src}`);
      continue;
    }
    try {
      mkdirSync(dirname(target), { recursive: true });
      writeFileSync(target, content);
      written += 1;
    } catch (e: any) {
      warnings.push(`write ${target}: ${e.message}`);
    }
  }
  return written;
}

function formatBatches(files: string[], json: boolean): Promise<void> {
  const maxArgLen = 50_000;
  let batch: string[] = [];
  let len = 0;
  const flush = async () => {
    if (batch.length === 0) return;
    const args = ["-y", "prettier", "--write", ...batch];
    const code = json
      ? await new Promise<number>((res) => {
          const p = spawn("npx", args, { stdio: ["ignore", "ignore", "pipe"] });
          let err = "";
          p.stderr?.on("data", (d) => (err += d.toString()));
          p.on("close", (c) => {
            if ((c ?? 1) !== 0) process.stderr.write(err);
            res(c ?? 1);
          });
          p.on("error", (e) => {
            process.stderr.write(e.message);
            res(1);
          });
        })
      : await runForwarded("npx", args);
    if (code !== 0) {
      process.stderr.write(
        `prettier batch exited with code ${code} (continuing)\n`
      );
    }
    batch = [];
    len = 0;
  };

  return (async () => {
    for (const f of files) {
      batch.push(f);
      len += f.length + 1;
      if (len >= maxArgLen) await flush();
    }
    await flush();
  })();
}

async function main(): Promise<void> {
  const started = Date.now();
  let opts: Options;
  try {
    opts = parseArgs(process.argv.slice(2));
  } catch (e: any) {
    process.stderr.write(`Error: ${e.message}\n`);
    process.exit(2);
  }

  let resolved: ResolvedApp;
  try {
    if (opts.asar) {
      const r = resolveByPath(opts.asar);
      if (!r) throw new Error(`--asar path not found: ${opts.asar}`);
      const appName =
        opts.app && !isAbsolute(opts.app)
          ? opts.app
          : appNameFromPath(opts.asar);
      resolved = { ...r, appName };
    } else {
      resolved = resolveApp(opts.app);
    }
  } catch (e: any) {
    fail(e.message, opts.json);
  }

  const outputDir = resolve(
    opts.output ??
      join(
        downloadsDir(),
        `${sanitizeAppName(resolved.appName)}-electron-extract`
      )
  );
  try {
    assertSafeOutputDir(outputDir, resolved.appName);
  } catch (e: any) {
    fail(e.message, opts.json);
  }

  const extractedDir = join(outputDir, "extracted");
  const unpackedOut = join(outputDir, "extracted.unpacked");
  const restoredDir = join(outputDir, "restored");

  if (opts.dryRun) {
    const summary = {
      status: "dry-run",
      appName: resolved.appName,
      asar: resolved.asarPath,
      unpacked: resolved.unpackedDir,
      output: outputDir,
      extracted: extractedDir,
      extractedUnpacked: opts.noUnpacked
        ? null
        : resolved.unpackedDir
        ? unpackedOut
        : null,
      restored: opts.skipRestore ? null : restoredDir,
    };
    if (opts.json) {
      process.stdout.write(JSON.stringify(summary) + "\n");
    } else {
      process.stdout.write(
        `[dry-run] App:        ${resolved.appName}\n` +
          `[dry-run] Asar:       ${resolved.asarPath}\n` +
          `[dry-run] Unpacked:   ${resolved.unpackedDir ?? "(none)"}\n` +
          `[dry-run] Output:     ${outputDir}\n` +
          `[dry-run]  extracted: ${extractedDir}\n` +
          `[dry-run]  unpacked:  ${
            opts.noUnpacked
              ? "(skipped)"
              : resolved.unpackedDir
              ? unpackedOut
              : "(none)"
          }\n` +
          `[dry-run]  restored:  ${
            opts.skipRestore ? "(skipped)" : restoredDir
          }\n`
      );
    }
    return;
  }

  if (existsSync(outputDir) && dirIsNonEmpty(outputDir) && !opts.force) {
    fail(
      `output directory exists and is not empty: ${outputDir}\n  Pass --force to allow writing into it, or choose another --output.`,
      opts.json
    );
  }
  mkdirSync(outputDir, { recursive: true });

  if (!opts.json) {
    process.stdout.write(`App:    ${resolved.appName}\n`);
    process.stdout.write(`Asar:   ${resolved.asarPath}\n`);
    process.stdout.write(`Output: ${outputDir}\n`);
    process.stdout.write(`Extracting asar...\n`);
  }

  try {
    await extractAsar(resolved.asarPath, extractedDir, opts.json);
  } catch (e: any) {
    fail(e.message, opts.json);
  }

  const counts: Counts = {
    extractedFiles: 0,
    restoredFiles: 0,
    formattedFiles: 0,
    skippedNodeModules: 0,
    unpackedFiles: 0,
  };
  const warnings: string[] = [];

  let unpackedFinal: string | null = null;
  if (
    !opts.noUnpacked &&
    resolved.unpackedDir &&
    existsAsDir(resolved.unpackedDir)
  ) {
    if (!opts.json) process.stdout.write(`Copying app.asar.unpacked...\n`);
    try {
      cpSync(resolved.unpackedDir, unpackedOut, { recursive: true });
      counts.unpackedFiles = countFiles(unpackedOut);
      unpackedFinal = unpackedOut;
    } catch (e: any) {
      warnings.push(`copy unpacked: ${e.message}`);
    }
  }

  const walked = { jsFiles: [] as string[], cssFiles: [] as string[] };
  walk(extractedDir, walked, counts);

  const toFormat: string[] = [];
  const restoredMapFiles = new Set<string>();
  const skipFormatSet = new Set<string>();

  if (!opts.skipRestore) {
    for (const js of walked.jsFiles) {
      const mapPath = js + ".map";
      if (!existsAsFile(mapPath)) continue;
      const w = restoreFromMap(mapPath, extractedDir, restoredDir, warnings);
      if (w > 0) {
        counts.restoredFiles += w;
        restoredMapFiles.add(mapPath);
        skipFormatSet.add(js);
        const license = js + ".LICENSE.txt";
        if (existsAsFile(license)) skipFormatSet.add(license);
      }
    }
  }

  if (!opts.skipFormat) {
    for (const js of walked.jsFiles)
      if (!skipFormatSet.has(js)) toFormat.push(js);
    for (const css of walked.cssFiles) toFormat.push(css);
    if (toFormat.length > 0) {
      if (!opts.json)
        process.stdout.write(
          `Formatting ${toFormat.length} file(s) with prettier...\n`
        );
      await formatBatches(toFormat, opts.json);
      counts.formattedFiles = toFormat.length;
    }
  }

  const report: Report = {
    appName: resolved.appName,
    source: {
      input: opts.app,
      asar: resolved.asarPath,
      platform: process.platform,
      installRoot: resolved.installRoot,
    },
    output: {
      root: outputDir,
      extracted: extractedDir,
      unpacked: unpackedFinal,
      restored: counts.restoredFiles > 0 ? restoredDir : null,
    },
    counts,
    warnings,
    durationMs: Date.now() - started,
  };

  try {
    writeFileSync(
      join(outputDir, "extract-report.json"),
      JSON.stringify(report, null, 2)
    );
  } catch (e: any) {
    warnings.push(`write extract-report.json: ${e.message}`);
  }

  if (opts.json) {
    process.stdout.write(JSON.stringify({ status: "ok", ...report }) + "\n");
  } else {
    process.stdout.write(
      `\nDone in ${(report.durationMs / 1000).toFixed(1)}s\n` +
        `  Extracted:        ${counts.extractedFiles} file(s) into ${extractedDir}\n` +
        (counts.unpackedFiles > 0
          ? `  Unpacked copied:  ${counts.unpackedFiles} file(s) into ${unpackedOut}\n`
          : "") +
        `  Restored:         ${counts.restoredFiles} file(s)` +
        (counts.restoredFiles > 0 ? ` into ${restoredDir}\n` : `\n`) +
        `  Formatted:        ${counts.formattedFiles} file(s)\n` +
        `  node_modules dirs skipped: ${counts.skippedNodeModules}\n` +
        (warnings.length > 0
          ? `  Warnings:         ${warnings.length} (see extract-report.json)\n`
          : "")
    );
  }
}

function isDirectRun(): boolean {
  if (import.meta.main) return true;
  const scriptPath = process.argv[1];
  return Boolean(
    scriptPath && pathToFileURL(resolve(scriptPath)).href === import.meta.url
  );
}

if (isDirectRun()) {
  main().catch((e) => {
    process.stderr.write(`Unexpected error: ${e?.stack ?? e}\n`);
    process.exit(1);
  });
}
