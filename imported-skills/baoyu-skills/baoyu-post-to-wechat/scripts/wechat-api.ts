import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import {
  loadWechatExtendConfig,
  resolveAccount,
  loadCredentials,
  type ResolvedAccount,
  type StrictHostKeyChecking,
} from "./wechat-extend-config.ts";
import {
  type WechatUploadAsset,
  prepareWechatBodyImageUpload,
  needsWechatBodyImageProcessing,
} from "./wechat-image-processor.ts";
import { loadUploadAsset } from "./wechat-image-loader.ts";
import { wechatHttp, buildMultipart, type WechatClient } from "./wechat-http.ts";
import {
  type RemotePublishConfig,
  normalizeRemoteConfig,
  withSshTunnel,
} from "./wechat-remote-publish.ts";

interface AccessTokenResponse {
  access_token?: string;
  errcode?: number;
  errmsg?: string;
}

interface UploadResponse {
  media_id: string;
  url: string;
  errcode?: number;
  errmsg?: string;
}

interface PublishResponse {
  media_id?: string;
  errcode?: number;
  errmsg?: string;
}

interface ImageInfo {
  placeholder: string;
  localPath: string;
  originalPath: string;
}

interface MarkdownRenderResult {
  title: string;
  author: string;
  summary: string;
  htmlPath: string;
  contentImages: ImageInfo[];
}

type ArticleType = "news" | "newspic";

interface ArticleOptions {
  title: string;
  author?: string;
  digest?: string;
  content: string;
  thumbMediaId: string;
  articleType: ArticleType;
  contentSourceUrl?: string;
  imageMediaIds?: string[];
  needOpenComment?: number;
  onlyFansCanComment?: number;
}

const TOKEN_URL = "https://api.weixin.qq.com/cgi-bin/token";
const UPLOAD_BODY_IMG_URL = "https://api.weixin.qq.com/cgi-bin/media/uploadimg";
const UPLOAD_MATERIAL_URL = "https://api.weixin.qq.com/cgi-bin/material/add_material";
const DRAFT_URL = "https://api.weixin.qq.com/cgi-bin/draft/add";

async function fetchAccessToken(
  appId: string,
  appSecret: string,
  client: WechatClient = wechatHttp,
): Promise<string> {
  const url = `${TOKEN_URL}?grant_type=client_credential&appid=${appId}&secret=${appSecret}`;
  const res = await client(url);
  if (res.status < 200 || res.status >= 300) {
    throw new Error(`Failed to fetch access token: ${res.status}`);
  }
  const data = await res.json<AccessTokenResponse>();
  if (data.errcode) {
    throw new Error(`Access token error ${data.errcode}: ${data.errmsg}`);
  }
  if (!data.access_token) {
    throw new Error("No access_token in response");
  }
  return data.access_token;
}

function toHttpsUrl(url: string | undefined): string {
  if (!url) return "";
  return url.startsWith("http://") ? url.replace(/^http:\/\//i, "https://") : url;
}

function htmlToPlainText(html: string): string {
  if (!html) return "";

  let text = html;

  // 1. 将 <br>, <br/>, <br /> 替换为换行符
  text = text.replace(/<br\s*\/?>/gi, "\n");

  // 2. 将 </p>, </div>, </h1>, </h2>, </h3>, </h4>, </h5>, </h6>, </li> 替换为换行符
  text = text.replace(/<\/(?:p|div|h[1-6]|li|tr|td|th)>/gi, "\n");

  // 3. 去掉所有剩余的 HTML 标签
  text = text.replace(/<[^>]+>/g, "");

  // 4. 解码 HTML 实体
  const entityMap: Record<string, string> = {
    "&nbsp;": " ",
    "&lt;": "<",
    "&gt;": ">",
    "&amp;": "&",
    "&quot;": '"',
    "&#39;": "'",
    "&apos;": "'",
    "&mdash;": "—",
    "&ndash;": "–",
    "&hellip;": "…",
    "&ldquo;": "“",
    "&rdquo;": "”",
    "&lsquo;": "‘",
    "&rsquo;": "’",
  };
  text = text.replace(/&(?:[a-zA-Z]+|#x[0-9a-fA-F]+|#\d+);/g, (entity) => {
    if (entityMap[entity]) return entityMap[entity];
    const hexMatch = entity.match(/^&#x([0-9a-fA-F]+);$/);
    if (hexMatch) {
      return String.fromCodePoint(Number.parseInt(hexMatch[1]!, 16));
    }
    const numMatch = entity.match(/^&#(\d+);$/);
    if (numMatch) {
      return String.fromCodePoint(Number.parseInt(numMatch[1]!, 10));
    }
    return entity;
  });

  // 5. 合并多个连续空白字符（空格、制表符、换行）为一个空格
  text = text.replace(/[ \t]+/g, " ");

  // 6. 合并多个连续换行为一个换行
  text = text.replace(/\n{3,}/g, "\n\n");

  // 7. 去掉行首行尾空白
  text = text.split("\n").map(line => line.trim()).join("\n");

  // 8. 最终 trim
  return text.trim();
}

async function uploadImage(
  imagePath: string,
  accessToken: string,
  baseDir?: string,
  uploadType: "body" | "material" = "body",
  client: WechatClient = wechatHttp,
): Promise<UploadResponse> {
  const asset = await loadUploadAsset(imagePath, baseDir);
  let uploadAsset = asset;

  if (uploadType === "body" && needsWechatBodyImageProcessing(asset)) {
    const prepared = await prepareWechatBodyImageUpload(asset);
    uploadAsset = {
      ...asset,
      buffer: prepared.buffer,
      filename: prepared.filename,
      contentType: prepared.contentType,
      fileExt: path.extname(prepared.filename).toLowerCase(),
      fileSize: prepared.buffer.length,
    };
    const note = prepared.processingNotes.join(", ");
    console.error(`[wechat-api] Processed ${asset.filename} for body upload: ${note}`);
  }

  const result = await uploadToWechat(
    uploadAsset.buffer,
    uploadAsset.filename,
    uploadAsset.contentType,
    accessToken,
    uploadType,
    client,
  );

  // media/uploadimg 接口只返回 URL，material/add_material 返回 media_id
  if (uploadType === "body") {
    return {
      url: toHttpsUrl(result.url),
      media_id: "",
    } as UploadResponse;
  } else {
    result.url = toHttpsUrl(result.url);
    return result;
  }
}

async function uploadToWechat(
  fileBuffer: Buffer,
  filename: string,
  contentType: string,
  accessToken: string,
  uploadType: "body" | "material",
  client: WechatClient = wechatHttp,
): Promise<UploadResponse> {
  const multipart = buildMultipart([
    { name: "media", filename, contentType, data: fileBuffer },
  ]);

  const uploadUrl = uploadType === "body" ? UPLOAD_BODY_IMG_URL : UPLOAD_MATERIAL_URL;
  const url = `${uploadUrl}?type=image&access_token=${accessToken}`;
  const res = await client(url, {
    method: "POST",
    headers: { "Content-Type": multipart.contentType },
    body: multipart.body,
  });

  const data = await res.json<UploadResponse>();
  if (data.errcode && data.errcode !== 0) {
    throw new Error(`Upload failed ${data.errcode}: ${data.errmsg}`);
  }

  return data;
}

async function uploadImagesInHtml(
  html: string,
  accessToken: string,
  baseDir: string,
  contentImages: ImageInfo[] = [],
  articleType: ArticleType = "news",
  collectNewsCoverFallback: boolean = false,
  client: WechatClient = wechatHttp,
): Promise<{ html: string; firstCoverMediaId: string; imageMediaIds: string[] }> {
  const imgRegex = /<img[^>]*\ssrc=["']([^"']+)["'][^>]*>/gi;
  const matches = [...html.matchAll(imgRegex)];

  if (matches.length === 0 && contentImages.length === 0) {
    return { html, firstCoverMediaId: "", imageMediaIds: [] };
  }

  let firstCoverMediaId = "";
  let updatedHtml = html;
  const imageMediaIds: string[] = [];
  const uploadedBySource = new Map<string, UploadResponse>();

  for (const match of matches) {
    const [fullTag, src] = match;
    if (!src) continue;

    if (src.startsWith("https://mmbiz.qpic.cn")) {
      if (collectNewsCoverFallback && !firstCoverMediaId) {
        try {
          const coverResp = await uploadImage(src, accessToken, baseDir, "material", client);
          firstCoverMediaId = coverResp.media_id;
        } catch (err) {
          console.error(`[wechat-api] Failed to reuse existing WeChat image as cover: ${src}`, err);
        }
      }
      continue;
    }

    const localPathMatch = fullTag.match(/data-local-path=["']([^"']+)["']/);
    const imagePath = localPathMatch ? localPathMatch[1]! : src;

    console.error(`[wechat-api] Uploading body image: ${imagePath}`);
    try {
      let resp = uploadedBySource.get(imagePath);
      if (!resp) {
        resp = await uploadImage(imagePath, accessToken, baseDir, "body", client);
        uploadedBySource.set(imagePath, resp);
      }
      const newTag = fullTag
        .replace(/\ssrc=["'][^"']+["']/, ` src="${resp.url}"`)
        .replace(/\sdata-local-path=["'][^"']+["']/, "");
      updatedHtml = updatedHtml.replace(fullTag, newTag);
      const shouldUploadMaterial = articleType === "newspic" || (collectNewsCoverFallback && !firstCoverMediaId);
      if (shouldUploadMaterial) {
        let materialResp = uploadedBySource.get(`${imagePath}:material`);
        if (!materialResp) {
          materialResp = await uploadImage(imagePath, accessToken, baseDir, "material", client);
          uploadedBySource.set(`${imagePath}:material`, materialResp);
        }
        if (articleType === "newspic" && materialResp.media_id) {
          imageMediaIds.push(materialResp.media_id);
        }
        if (collectNewsCoverFallback && !firstCoverMediaId && materialResp.media_id) {
          firstCoverMediaId = materialResp.media_id;
        }
      }
    } catch (err) {
      console.error(`[wechat-api] Failed to upload ${imagePath}:`, err);
    }
  }

  for (const image of contentImages) {
    if (!updatedHtml.includes(image.placeholder)) continue;

    const imagePath = image.localPath || image.originalPath;
    console.error(`[wechat-api] Uploading body image: ${imagePath}`);

    try {
      let resp = uploadedBySource.get(imagePath);
      if (!resp) {
        resp = await uploadImage(imagePath, accessToken, baseDir, "body", client);
        uploadedBySource.set(imagePath, resp);
      }

      const replacementTag = `<img src="${resp.url}" style="display: block; width: 100%; margin: 1.5em auto;">`;
      updatedHtml = replaceAllPlaceholders(updatedHtml, image.placeholder, replacementTag);
      const shouldUploadMaterial = articleType === "newspic" || (collectNewsCoverFallback && !firstCoverMediaId);
      if (shouldUploadMaterial) {
        let materialResp = uploadedBySource.get(`${imagePath}:material`);
        if (!materialResp) {
          materialResp = await uploadImage(imagePath, accessToken, baseDir, "material", client);
          uploadedBySource.set(`${imagePath}:material`, materialResp);
        }
        if (articleType === "newspic" && materialResp.media_id) {
          imageMediaIds.push(materialResp.media_id);
        }
        if (collectNewsCoverFallback && !firstCoverMediaId && materialResp.media_id) {
          firstCoverMediaId = materialResp.media_id;
        }
      }
    } catch (err) {
      console.error(`[wechat-api] Failed to upload placeholder ${image.placeholder}:`, err);
    }
  }

  return { html: updatedHtml, firstCoverMediaId, imageMediaIds };
}

async function publishToDraft(
  options: ArticleOptions,
  accessToken: string,
  client: WechatClient = wechatHttp,
): Promise<PublishResponse> {
  const url = `${DRAFT_URL}?access_token=${accessToken}`;

  let article: Record<string, unknown>;

  const noc = options.needOpenComment ?? 1;
  const ofcc = options.onlyFansCanComment ?? 0;

  if (options.articleType === "newspic") {
    if (!options.imageMediaIds || options.imageMediaIds.length === 0) {
      throw new Error("newspic requires at least one image");
    }
    // newspic 的 content 应该是纯文本，需要：
    // 1. 去掉 HTML 标签
    // 2. 解码 HTML 实体（&nbsp;、&lt; 等）
    // 3. 合并多余空白字符
    const plainContent = htmlToPlainText(options.content);
    article = {
      article_type: "newspic",
      title: options.title,
      content: plainContent,
      need_open_comment: noc,
      only_fans_can_comment: ofcc,
      image_info: {
        image_list: options.imageMediaIds.map(id => ({ image_media_id: id })),
      },
    };
    if (options.author) article.author = options.author;
  } else {
    article = {
      article_type: "news",
      title: options.title,
      content: options.content,
      thumb_media_id: options.thumbMediaId,
      need_open_comment: noc,
      only_fans_can_comment: ofcc,
    };
    if (options.author) article.author = options.author;
    if (options.digest) article.digest = options.digest;
    if (options.contentSourceUrl) article.content_source_url = options.contentSourceUrl;
  }

  const res = await client(url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ articles: [article] }),
  });

  const data = await res.json<PublishResponse>();
  if (data.errcode && data.errcode !== 0) {
    throw new Error(`Publish failed ${data.errcode}: ${data.errmsg}`);
  }

  return data;
}

function parseFrontmatter(content: string): { frontmatter: Record<string, string>; body: string } {
  const match = content.match(/^\s*---\r?\n([\s\S]*?)\r?\n---\r?\n?([\s\S]*)$/);
  if (!match) return { frontmatter: {}, body: content };

  const frontmatter: Record<string, string> = {};
  const lines = match[1]!.split("\n");
  for (const line of lines) {
    const colonIdx = line.indexOf(":");
    if (colonIdx > 0) {
      const key = line.slice(0, colonIdx).trim();
      let value = line.slice(colonIdx + 1).trim();
      if ((value.startsWith('"') && value.endsWith('"')) ||
          (value.startsWith("'") && value.endsWith("'"))) {
        value = value.slice(1, -1);
      }
      frontmatter[key] = value;
    }
  }

  return { frontmatter, body: match[2]! };
}

function renderMarkdownWithPlaceholders(
  markdownPath: string,
  theme: string = "default",
  color?: string,
  citeStatus: boolean = true,
  title?: string,
): MarkdownRenderResult {
  const __filename = fileURLToPath(import.meta.url);
  const __dirname = path.dirname(__filename);
  const mdToWechatScript = path.join(__dirname, "md-to-wechat.ts");
  const baseDir = path.dirname(markdownPath);

  const args = ["-y", "bun", mdToWechatScript, markdownPath];
  if (title) args.push("--title", title);
  if (theme) args.push("--theme", theme);
  if (color) args.push("--color", color);
  if (!citeStatus) args.push("--no-cite");

  console.error(`[wechat-api] Rendering markdown with placeholders via md-to-wechat: ${theme}${color ? `, color: ${color}` : ""}, citeStatus: ${citeStatus}`);
  const result = spawnSync("npx", args, {
    stdio: ["inherit", "pipe", "pipe"],
    cwd: baseDir,
  });

  if (result.status !== 0) {
    const stderr = result.stderr?.toString() || "";
    throw new Error(`Markdown placeholder render failed: ${stderr}`);
  }

  const stdout = result.stdout?.toString() || "";
  return JSON.parse(stdout) as MarkdownRenderResult;
}

function replaceAllPlaceholders(html: string, placeholder: string, replacement: string): string {
  const escapedPlaceholder = placeholder.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return html.replace(new RegExp(escapedPlaceholder + "(?!\\d)", "g"), replacement);
}

function extractHtmlContent(htmlPath: string): string {
  const html = fs.readFileSync(htmlPath, "utf-8");
  const match = html.match(/<div id="output">([\s\S]*?)<\/div>\s*<\/body>/);
  if (match) {
    return match[1]!.trim();
  }
  const bodyMatch = html.match(/<body[^>]*>([\s\S]*?)<\/body>/i);
  return bodyMatch ? bodyMatch[1]!.trim() : html;
}

function printUsage(): never {
  console.log(`Publish article to WeChat Official Account draft using API

Usage:
  npx -y bun wechat-api.ts <file> [options]

Arguments:
  file                Markdown (.md) or HTML (.html) file

Options:
  --type <type>       Article type: news (文章, default) or newspic (图文)
  --title <title>     Override title
  --author <name>     Author name (max 16 chars)
  --summary <text>    Article summary/digest (max 128 chars)
  --source-url <url>  Original article URL ("阅读原文" link, max 1KB)
  --theme <name>      Theme name for markdown (default, grace, simple, modern). Default: default
  --color <name|hex>  Primary color (blue, green, vermilion, etc. or hex)
  --cover <path>      Cover image path (local or URL)
  --account <alias>   Select account by alias (for multi-account setups)
  --no-cite           Disable bottom citations for ordinary external links in markdown mode
  --dry-run           Parse and render only, don't publish
  --remote            Route WeChat API calls via SSH SOCKS5 tunnel to a whitelisted server
  --remote-host <h>   Remote server host (implies --remote)
  --remote-user <u>   SSH user (default: root, implies --remote)
  --remote-port <n>   SSH port (default: 22, implies --remote)
  --remote-identity-file <p>           SSH private key path (implies --remote)
  --remote-known-hosts-file <p>        SSH known_hosts file path (implies --remote)
  --remote-strict-host-key-checking <yes|no|accept-new> (implies --remote)
  --remote-connect-timeout <seconds>   SSH ConnectTimeout (implies --remote)
  --remote-proxy-jump <spec>           SSH ProxyJump value (implies --remote)
  --help              Show this help

Frontmatter Fields (markdown):
  title               Article title
  author              Author name
  digest/summary      Article summary
  sourceUrl/contentSourceUrl/content_source_url   Original article URL
  coverImage/featureImage/cover/image   Cover image path

Comments:
  Comments are enabled by default, open to all users.

Environment Variables:
  WECHAT_APP_ID       WeChat App ID
  WECHAT_APP_SECRET   WeChat App Secret

Config File Locations (in priority order):
  1. Environment variables
  2. <cwd>/.baoyu-skills/.env
  3. ~/.baoyu-skills/.env

Example:
  npx -y bun wechat-api.ts article.md
  npx -y bun wechat-api.ts article.md --theme grace --cover cover.png
  npx -y bun wechat-api.ts article.md --author "Author Name" --summary "Brief intro" --source-url "https://example.com/original"
  npx -y bun wechat-api.ts article.html --title "My Article"
  npx -y bun wechat-api.ts images/ --type newspic --title "Photo Album"
  npx -y bun wechat-api.ts article.md --dry-run
  npx -y bun wechat-api.ts article.md --no-cite
`);
  process.exit(0);
}

interface CliArgs {
  filePath: string;
  isHtml: boolean;
  articleType: ArticleType;
  title?: string;
  author?: string;
  summary?: string;
  sourceUrl?: string;
  theme: string;
  color?: string;
  cover?: string;
  account?: string;
  citeStatus: boolean;
  dryRun: boolean;
  remote: boolean;
  remoteHost?: string;
  remoteUser?: string;
  remotePort?: number;
  remoteIdentityFile?: string;
  remoteKnownHostsFile?: string;
  remoteStrictHostKeyChecking?: StrictHostKeyChecking;
  remoteConnectTimeout?: number;
  remoteProxyJump?: string;
}

function parseArgs(argv: string[]): CliArgs {
  if (argv.length === 0 || argv.includes("--help") || argv.includes("-h")) {
    printUsage();
  }

  const args: CliArgs = {
    filePath: "",
    isHtml: false,
    articleType: "news",
    theme: "default",
    citeStatus: true,
    dryRun: false,
    remote: false,
  };

  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i]!;
    if (arg === "--type" && argv[i + 1]) {
      const t = argv[++i]!.toLowerCase();
      if (t === "news" || t === "newspic") {
        args.articleType = t;
      }
    } else if (arg === "--title" && argv[i + 1]) {
      args.title = argv[++i];
    } else if (arg === "--author" && argv[i + 1]) {
      args.author = argv[++i];
    } else if (arg === "--summary" && argv[i + 1]) {
      args.summary = argv[++i];
    } else if (arg === "--source-url" && argv[i + 1]) {
      args.sourceUrl = argv[++i];
    } else if (arg === "--theme" && argv[i + 1]) {
      args.theme = argv[++i]!;
    } else if (arg === "--color" && argv[i + 1]) {
      args.color = argv[++i];
    } else if (arg === "--cover" && argv[i + 1]) {
      args.cover = argv[++i];
    } else if (arg === "--account" && argv[i + 1]) {
      args.account = argv[++i];
    } else if (arg === "--cite") {
      args.citeStatus = true;
    } else if (arg === "--no-cite") {
      args.citeStatus = false;
    } else if (arg === "--dry-run") {
      args.dryRun = true;
    } else if (arg === "--remote") {
      args.remote = true;
    } else if (arg === "--remote-host" && argv[i + 1]) {
      args.remoteHost = argv[++i];
      args.remote = true;
    } else if (arg === "--remote-user" && argv[i + 1]) {
      args.remoteUser = argv[++i];
      args.remote = true;
    } else if (arg === "--remote-port" && argv[i + 1]) {
      const n = Number.parseInt(argv[++i]!, 10);
      if (!Number.isInteger(n) || n < 1 || n > 65535) {
        console.error(`Error: --remote-port must be 1-65535, got ${argv[i]}`);
        process.exit(1);
      }
      args.remotePort = n;
      args.remote = true;
    } else if (arg === "--remote-identity-file" && argv[i + 1]) {
      args.remoteIdentityFile = argv[++i];
      args.remote = true;
    } else if (arg === "--remote-known-hosts-file" && argv[i + 1]) {
      args.remoteKnownHostsFile = argv[++i];
      args.remote = true;
    } else if (arg === "--remote-strict-host-key-checking" && argv[i + 1]) {
      const v = argv[++i]!.toLowerCase();
      if (v !== "yes" && v !== "no" && v !== "accept-new") {
        console.error(`Error: --remote-strict-host-key-checking must be yes|no|accept-new, got ${argv[i]}`);
        process.exit(1);
      }
      args.remoteStrictHostKeyChecking = v as StrictHostKeyChecking;
      args.remote = true;
    } else if (arg === "--remote-connect-timeout" && argv[i + 1]) {
      const n = Number.parseInt(argv[++i]!, 10);
      if (!Number.isInteger(n) || n <= 0) {
        console.error(`Error: --remote-connect-timeout must be a positive integer, got ${argv[i]}`);
        process.exit(1);
      }
      args.remoteConnectTimeout = n;
      args.remote = true;
    } else if (arg === "--remote-proxy-jump" && argv[i + 1]) {
      args.remoteProxyJump = argv[++i];
      args.remote = true;
    } else if (arg.startsWith("--") && argv[i + 1] && !argv[i + 1]!.startsWith("-")) {
      i++;
    } else if (!arg.startsWith("-")) {
      args.filePath = arg;
    }
  }

  if (!args.filePath) {
    console.error("Error: File path required");
    process.exit(1);
  }

  args.isHtml = args.filePath.toLowerCase().endsWith(".html");

  return args;
}

function extractHtmlTitle(html: string): string {
  const titleMatch = html.match(/<title>([^<]+)<\/title>/i);
  if (titleMatch) return titleMatch[1]!;
  const h1Match = html.match(/<h1[^>]*>([^<]+)<\/h1>/i);
  if (h1Match) return h1Match[1]!.replace(/<[^>]+>/g, "").trim();
  return "";
}

function buildRemoteConfig(args: CliArgs, resolved: ResolvedAccount): RemotePublishConfig {
  const host = args.remoteHost ?? resolved.remote_publish_host;
  if (!host) {
    throw new Error(
      "Remote publishing requires a host. Set --remote-host, EXTEND.md remote_publish_host, " +
      "or an account-level remote_publish_host.",
    );
  }
  return {
    host,
    user: args.remoteUser ?? resolved.remote_publish_user,
    port: args.remotePort ?? resolved.remote_publish_port,
    identityFile: args.remoteIdentityFile ?? resolved.remote_publish_identity_file,
    knownHostsFile: args.remoteKnownHostsFile ?? resolved.remote_publish_known_hosts_file,
    strictHostKeyChecking:
      args.remoteStrictHostKeyChecking ?? resolved.remote_publish_strict_host_key_checking,
    connectTimeout: args.remoteConnectTimeout ?? resolved.remote_publish_connect_timeout,
    proxyJump: args.remoteProxyJump ?? resolved.remote_publish_proxy_jump,
  };
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv.slice(2));

  const filePath = path.resolve(args.filePath);
  if (!fs.existsSync(filePath)) {
    console.error(`Error: File not found: ${filePath}`);
    process.exit(1);
  }

  const baseDir = path.dirname(filePath);
  let title = args.title || "";
  let author = args.author || "";
  let digest = args.summary || "";
  let sourceUrl = args.sourceUrl || "";
  let htmlPath: string;
  let htmlContent: string;
  let frontmatter: Record<string, string> = {};
  let contentImages: ImageInfo[] = [];

  if (args.isHtml) {
    htmlPath = filePath;
    htmlContent = extractHtmlContent(htmlPath);
    const mdPath = filePath.replace(/\.html$/i, ".md");
    if (fs.existsSync(mdPath)) {
      const mdContent = fs.readFileSync(mdPath, "utf-8");
      const parsed = parseFrontmatter(mdContent);
      frontmatter = parsed.frontmatter;
      if (!title && frontmatter.title) title = frontmatter.title;
      if (!author) author = frontmatter.author || "";
      if (!digest) digest = frontmatter.digest || frontmatter.summary || frontmatter.description || "";
      if (!sourceUrl) sourceUrl = frontmatter.sourceUrl || frontmatter.contentSourceUrl || frontmatter.content_source_url || "";
    }
    if (!title) {
      title = extractHtmlTitle(fs.readFileSync(htmlPath, "utf-8"));
    }
    console.error(`[wechat-api] Using HTML file: ${htmlPath}`);
  } else {
    const content = fs.readFileSync(filePath, "utf-8");
    const parsed = parseFrontmatter(content);
    frontmatter = parsed.frontmatter;
    const body = parsed.body;

    title = title || frontmatter.title || "";
    if (!title) {
      const h1Match = body.match(/^#\s+(.+)$/m);
      if (h1Match) title = h1Match[1]!;
    }
    if (!author) author = frontmatter.author || "";
    if (!digest) digest = frontmatter.digest || frontmatter.summary || frontmatter.description || "";
    if (!sourceUrl) sourceUrl = frontmatter.sourceUrl || frontmatter.contentSourceUrl || frontmatter.content_source_url || "";

    console.error(`[wechat-api] Theme: ${args.theme}${args.color ? `, color: ${args.color}` : ""}, citeStatus: ${args.citeStatus}`);
    const rendered = renderMarkdownWithPlaceholders(filePath, args.theme, args.color, args.citeStatus, args.title);
    htmlPath = rendered.htmlPath;
    contentImages = rendered.contentImages;
    if (!title) title = rendered.title;
    if (!author) author = rendered.author;
    if (!digest) digest = rendered.summary;
    console.error(`[wechat-api] HTML generated: ${htmlPath}`);
    console.error(`[wechat-api] Placeholder images: ${contentImages.length}`);
    htmlContent = extractHtmlContent(htmlPath);
  }

  if (!title) {
    console.error("Error: No title found. Provide via --title, frontmatter, or <title> tag.");
    process.exit(1);
  }

  if (digest && digest.length > 120) {
    const truncated = digest.slice(0, 117);
    const lastPunct = Math.max(truncated.lastIndexOf("。"), truncated.lastIndexOf("，"), truncated.lastIndexOf("；"), truncated.lastIndexOf("、"));
    digest = lastPunct > 80 ? truncated.slice(0, lastPunct + 1) : truncated + "...";
    console.error(`[wechat-api] Digest truncated to ${digest.length} chars`);
  }

  console.error(`[wechat-api] Title: ${title}`);
  if (author) console.error(`[wechat-api] Author: ${author}`);
  if (digest) console.error(`[wechat-api] Digest: ${digest.slice(0, 50)}...`);
  if (sourceUrl) console.error(`[wechat-api] Source URL: ${sourceUrl}`);
  console.error(`[wechat-api] Type: ${args.articleType}`);

  const extConfig = loadWechatExtendConfig();
  const resolved = resolveAccount(extConfig, args.account);
  if (resolved.name) console.error(`[wechat-api] Account: ${resolved.name} (${resolved.alias})`);

  if (!author && resolved.default_author) author = resolved.default_author;

  if (args.dryRun) {
    console.log(JSON.stringify({
      articleType: args.articleType,
      title,
      author: author || undefined,
      digest: digest || undefined,
      sourceUrl: sourceUrl || undefined,
      htmlPath,
      contentLength: htmlContent.length,
      placeholderImageCount: contentImages.length || undefined,
      account: resolved.alias || undefined,
    }, null, 2));
    return;
  }

  const creds = loadCredentials(resolved);
  for (const skippedSource of creds.skippedSources) {
    console.error(`[wechat-api] Skipped incomplete credential source: ${skippedSource}`);
  }
  console.error(`[wechat-api] Credentials source: ${creds.source}`);

  const rawCoverPath = args.cover ||
    frontmatter.coverImage ||
    frontmatter.featureImage ||
    frontmatter.cover ||
    frontmatter.image;
  const coverPath = rawCoverPath && !path.isAbsolute(rawCoverPath) && args.cover
    ? path.resolve(process.cwd(), rawCoverPath)
    : rawCoverPath;
  const needNewsCoverFallback = args.articleType === "news" && !coverPath;

  const useRemote = args.remote || resolved.default_publish_method === "remote-api";
  const method = useRemote ? "remote-api" : "api";

  const publishWith = async (client: WechatClient): Promise<void> => {
    console.error("[wechat-api] Fetching access token...");
    const accessToken = await fetchAccessToken(creds.appId, creds.appSecret, client);

    console.error("[wechat-api] Uploading body images...");
    const { html: processedHtml, firstCoverMediaId, imageMediaIds } = await uploadImagesInHtml(
      htmlContent,
      accessToken,
      baseDir,
      contentImages,
      args.articleType,
      needNewsCoverFallback,
      client,
    );
    htmlContent = processedHtml;

    let thumbMediaId = "";

    if (coverPath) {
      console.error(`[wechat-api] Uploading cover: ${coverPath}`);
      const coverResp = await uploadImage(coverPath, accessToken, baseDir, "material", client);
      thumbMediaId = coverResp.media_id;
      console.error(`[wechat-api] Cover uploaded successfully, media_id: ${thumbMediaId}`);
    } else if (firstCoverMediaId && args.articleType === "news") {
      thumbMediaId = firstCoverMediaId;
      console.error(`[wechat-api] Using first body image as cover (fallback), media_id: ${thumbMediaId}`);
    }

    if (args.articleType === "news" && !thumbMediaId) {
      throw new Error("No cover image. Provide via --cover, frontmatter.coverImage, or include an image in content.");
    }

    if (args.articleType === "newspic" && imageMediaIds.length === 0) {
      throw new Error("newspic requires at least one image in content.");
    }

    console.error("[wechat-api] Publishing to draft...");
    const result = await publishToDraft({
      title,
      author: author || undefined,
      digest: digest || undefined,
      content: htmlContent,
      thumbMediaId,
      articleType: args.articleType,
      contentSourceUrl: sourceUrl || undefined,
      imageMediaIds: args.articleType === "newspic" ? imageMediaIds : undefined,
      needOpenComment: resolved.need_open_comment,
      onlyFansCanComment: resolved.only_fans_can_comment,
    }, accessToken, client);

    console.log(JSON.stringify({
      success: true,
      media_id: result.media_id,
      title,
      articleType: args.articleType,
      method,
    }, null, 2));

    console.error(`[wechat-api] Published successfully! media_id: ${result.media_id}`);
  };

  if (useRemote) {
    const remoteConfig = normalizeRemoteConfig(buildRemoteConfig(args, resolved));
    console.error(
      `[wechat-api] Remote publishing via ${remoteConfig.user}@${remoteConfig.host}:${remoteConfig.port}`,
    );
    await withSshTunnel(remoteConfig, async (client) => {
      await publishWith(client);
    });
  } else {
    await publishWith(wechatHttp);
  }
}

await main().catch((err) => {
  console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
  process.exit(1);
});
