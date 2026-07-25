import { mkdirSync, readFileSync, writeFileSync } from "fs"
import { dirname, join } from "path"
import MarkdownIt from "markdown-it"

type BlockKind =
  | "heading"
  | "thematicBreak"
  | "html"
  | "code"
  | "flow"

interface Block {
  kind: BlockKind
  md: string
  words: number
}

interface Chunk {
  blocks: Block[]
  words: number
}

export interface ChunkCliOptions {
  file: string
  maxWords: number
  outputDir: string
}

export interface ChunkResult {
  source: string
  chunks: number
  output_dir: string
  frontmatter: boolean
  words_per_chunk: number[]
}

const parser = new MarkdownIt({ html: true })

export function formatChunkUsage(command: string): string {
  return `Usage: ${command} <file> [--max-words 5000] [--output-dir <dir>]`
}

export function runChunkCli(args: string[], command = "chunk.ts"): number {
  const parsed = parseChunkCliArgs(args)

  if ("help" in parsed) {
    console.log(formatChunkUsage(command))
    return 0
  }

  if ("error" in parsed) {
    console.error(parsed.error)
    console.error(formatChunkUsage(command))
    return 1
  }

  const result = chunkMarkdownFile(parsed.file, {
    maxWords: parsed.maxWords,
    outputDir: parsed.outputDir,
  })

  console.log(JSON.stringify(result))
  return 0
}

export function chunkMarkdownFile(
  file: string,
  options: { maxWords?: number; outputDir?: string } = {}
): ChunkResult {
  const maxWords = options.maxWords ?? 5000
  const outputDir = options.outputDir ?? ""

  const rawContent = normalizeNewlines(readFileSync(file, "utf-8"))
  const { frontmatter, body } = extractFrontmatter(rawContent)
  const chunks = buildChunks(parseMarkdown(body), maxWords)

  const dir = outputDir ? join(outputDir, "chunks") : join(dirname(file), "chunks")
  mkdirSync(dir, { recursive: true })

  if (frontmatter) {
    writeFileSync(join(dir, "frontmatter.md"), frontmatter)
  }

  chunks.forEach((chunk, index) => {
    const num = String(index + 1).padStart(2, "0")
    writeFileSync(join(dir, `chunk-${num}.md`), chunk.blocks.map(block => block.md).join("\n\n"))
  })

  return {
    source: file,
    chunks: chunks.length,
    output_dir: dir,
    frontmatter: Boolean(frontmatter),
    words_per_chunk: chunks.map(chunk => chunk.words),
  }
}

function parseChunkCliArgs(args: string[]):
  | ChunkCliOptions
  | { help: true }
  | { error: string } {
  let file = ""
  let maxWords = 5000
  let outputDir = ""

  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index]

    if (arg === "-h" || arg === "--help") {
      return { help: true }
    }

    if (arg === "--max-words") {
      const value = args[index + 1]
      if (!value) return { error: "Missing value for --max-words" }
      maxWords = parsePositiveInt(value, 0)
      if (maxWords <= 0) return { error: `Invalid --max-words value: ${value}` }
      index += 1
      continue
    }

    if (arg === "--output-dir") {
      const value = args[index + 1]
      if (!value) return { error: "Missing value for --output-dir" }
      outputDir = value
      index += 1
      continue
    }

    if (arg.startsWith("-")) {
      return { error: `Unknown option: ${arg}` }
    }

    if (!file) {
      file = arg
      continue
    }

    return { error: `Unexpected positional argument: ${arg}` }
  }

  if (!file) {
    return { error: "Missing input file" }
  }

  return { file, maxWords, outputDir }
}

function parsePositiveInt(value: string | undefined, fallback: number): number {
  if (!value) return fallback
  const parsed = Number.parseInt(value, 10)
  return Number.isFinite(parsed) && parsed > 0 ? parsed : fallback
}

function normalizeNewlines(text: string): string {
  return text.replace(/^\uFEFF/, "").replace(/\r\n?/g, "\n")
}

function trimBoundaryBlankLines(text: string): string {
  return text.replace(/^\n+/, "").replace(/\n+$/, "")
}

function extractFrontmatter(content: string): { frontmatter: string; body: string } {
  const lines = content.split("\n")
  if (lines[0] !== "---") {
    return { frontmatter: "", body: content }
  }

  for (let index = 1; index < lines.length; index += 1) {
    if (lines[index] === "---" || lines[index] === "...") {
      return {
        frontmatter: lines.slice(0, index + 1).join("\n"),
        body: lines.slice(index + 1).join("\n").replace(/^\n+/, ""),
      }
    }
  }

  return { frontmatter: "", body: content }
}

function parseMarkdown(content: string): Block[] {
  if (!content.trim()) return []

  const lines = content.split("\n")
  const tokens = parser.parse(content, {})
  const blocks: Block[] = []

  for (const token of tokens) {
    if (!token.map || token.level !== 0) continue
    if (token.nesting !== 1 && token.nesting !== 0) continue

    const [startLine, endLine] = token.map
    const md = trimBoundaryBlankLines(lines.slice(startLine, endLine).join("\n"))
    if (!md) continue

    blocks.push(makeBlock(tokenTypeToBlockKind(token.type), md))
  }

  if (blocks.length === 0) {
    const body = trimBoundaryBlankLines(content)
    if (body) {
      blocks.push(makeBlock("flow", body))
    }
  }

  return blocks
}

function tokenTypeToBlockKind(tokenType: string): BlockKind {
  if (tokenType === "heading_open") return "heading"
  if (tokenType === "hr") return "thematicBreak"
  if (tokenType === "html_block") return "html"
  if (tokenType === "fence" || tokenType === "code_block") return "code"
  return "flow"
}

function makeBlock(kind: BlockKind, md: string): Block {
  return {
    kind,
    md: trimBoundaryBlankLines(md),
    words: countWords(md),
  }
}

function buildChunks(blocks: Block[], maxWordsPerChunk: number): Chunk[] {
  const sections = splitIntoSections(blocks)
  const normalizedBlocks: Block[] = []

  for (const section of sections) {
    const sectionWords = section.reduce((sum, block) => sum + block.words, 0)
    if (sectionWords <= maxWordsPerChunk) {
      normalizedBlocks.push(makeBlock("flow", section.map(block => block.md).join("\n\n")))
      continue
    }

    for (const block of section) {
      normalizedBlocks.push(...splitOversizedBlock(block, maxWordsPerChunk))
    }
  }

  const chunks: Chunk[] = []
  let currentBlocks: Block[] = []
  let currentWords = 0

  for (const block of normalizedBlocks) {
    if (currentWords + block.words > maxWordsPerChunk && currentBlocks.length > 0) {
      chunks.push({ blocks: currentBlocks, words: currentWords })
      currentBlocks = [block]
      currentWords = block.words
      continue
    }

    currentBlocks.push(block)
    currentWords += block.words
  }

  if (currentBlocks.length > 0) {
    chunks.push({ blocks: currentBlocks, words: currentWords })
  }

  return chunks
}

function splitIntoSections(blocks: Block[]): Block[][] {
  const sections: Block[][] = []
  let current: Block[] = []

  for (const block of blocks) {
    if (block.kind === "heading" && current.length > 0) {
      sections.push(current)
      current = [block]
      continue
    }

    current.push(block)
  }

  if (current.length > 0) {
    sections.push(current)
  }

  return sections
}

function splitOversizedBlock(block: Block, maxWordsPerChunk: number): Block[] {
  if (block.words <= maxWordsPerChunk) return [block]

  if (
    block.kind === "heading"
    || block.kind === "thematicBreak"
    || block.kind === "html"
    || block.kind === "code"
  ) {
    return [block]
  }

  const lines = block.md.split("\n")
  if (lines.length <= 1) {
    return [block]
  }

  const splitBlocks: Block[] = []
  let buffer: string[] = []
  let bufferWords = 0

  for (const line of lines) {
    const lineWords = countWords(line)
    if (bufferWords + lineWords > maxWordsPerChunk && buffer.length > 0) {
      splitBlocks.push(makeBlock(block.kind, buffer.join("\n")))
      buffer = [line]
      bufferWords = lineWords
      continue
    }

    buffer.push(line)
    bufferWords += lineWords
  }

  if (buffer.length > 0) {
    splitBlocks.push(makeBlock(block.kind, buffer.join("\n")))
  }

  return splitBlocks
}

function countWords(text: string): number {
  const cleaned = text.replace(/[#*`\[\]()>|_~-]/g, " ")
  const cjk = cleaned.match(/[\u4e00-\u9fff\u3400-\u4dbf\uf900-\ufaff]/g)
  const latin = cleaned.match(/[a-zA-Z0-9]+/g)
  return (cjk?.length ?? 0) + (latin?.length ?? 0)
}

if (import.meta.main) {
  process.exit(runChunkCli(process.argv.slice(2), process.argv[1] ?? "chunk.ts"))
}
