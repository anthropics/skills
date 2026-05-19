// Fetches the Wikipedia "Signs of AI writing" article (or any override
// URL) as parseable text. Uses the MediaWiki action API rather than
// scraping HTML — it returns clean wikitext, which is far easier to
// pattern-match than rendered HTML with templates expanded.
//
// Cache: ~/.cache/ai-tells-validator/wiki.{md,json}. Refetches by default
// when older than 1h; --fresh forces; --cache-ok skips network entirely.

import { mkdirSync, readFileSync, statSync, writeFileSync, existsSync } from 'node:fs'
import { homedir } from 'node:os'
import { join } from 'node:path'

const DEFAULT_URL = 'https://en.wikipedia.org/wiki/Wikipedia:Signs_of_AI_writing'
const CACHE_DIR = join(homedir(), '.cache', 'ai-tells-validator')
const CACHE_TEXT = join(CACHE_DIR, 'wiki.md')
const CACHE_META = join(CACHE_DIR, 'wiki.meta.json')
const ONE_HOUR_MS = 60 * 60 * 1000

export async function fetchWiki(options = {}) {
  const url = options.source ?? DEFAULT_URL
  const cacheOk = options.cacheOk === true
  const fresh = options.fresh === true

  if (cacheOk && existsSync(CACHE_TEXT)) {
    return readCache()
  }

  if (!fresh && existsSync(CACHE_TEXT) && existsSync(CACHE_META)) {
    const meta = readCacheMeta()
    if (meta && meta.url === url && Date.now() - meta.fetched_at_ms < ONE_HOUR_MS) {
      return readCache()
    }
  }

  // Wikipedia API: ?action=parse&page=...&prop=wikitext&format=json
  // Page-title path is more robust than URL-derived because the URL form
  // can change (e.g. moves), but the Wikipedia: namespace page survives.
  const title = extractWikipediaTitle(url) ?? 'Wikipedia:Signs_of_AI_writing'
  const apiUrl = `https://en.wikipedia.org/w/api.php?action=parse&page=${encodeURIComponent(title)}&prop=wikitext&format=json&formatversion=2`

  let response
  try {
    response = await fetch(apiUrl, {
      headers: {
        'User-Agent':
          'ai-tells-validator/0.1 (https://github.com/example/ai-tells-validator; refer to docs for contact)',
        Accept: 'application/json',
      },
    })
  } catch (err) {
    // Network failure → fall back to cache if we have one, else throw.
    if (existsSync(CACHE_TEXT)) {
      console.warn(`[wiki-fetch] network error (${err.message}); using stale cache`)
      return readCache()
    }
    throw new Error(`wiki_fetch_failed:${err.message}`)
  }
  if (!response.ok) {
    if (existsSync(CACHE_TEXT)) {
      console.warn(`[wiki-fetch] HTTP ${response.status}; using stale cache`)
      return readCache()
    }
    throw new Error(`wiki_fetch_http_${response.status}`)
  }
  const json = await response.json()
  const wikitext = json?.parse?.wikitext
  if (!wikitext || typeof wikitext !== 'string') {
    if (existsSync(CACHE_TEXT)) {
      console.warn('[wiki-fetch] empty wikitext response; using stale cache')
      return readCache()
    }
    throw new Error('wiki_fetch_empty_wikitext')
  }

  // Persist for next call.
  mkdirSync(CACHE_DIR, { recursive: true })
  writeFileSync(CACHE_TEXT, wikitext, 'utf-8')
  const meta = {
    url,
    title,
    fetched_at_ms: Date.now(),
    fetched_at_iso: new Date().toISOString(),
    bytes: Buffer.byteLength(wikitext, 'utf-8'),
  }
  writeFileSync(CACHE_META, JSON.stringify(meta, null, 2), 'utf-8')
  return { text: wikitext, meta }
}

function readCache() {
  const text = readFileSync(CACHE_TEXT, 'utf-8')
  const meta = readCacheMeta() ?? {
    url: DEFAULT_URL,
    fetched_at_ms: statSync(CACHE_TEXT).mtimeMs,
    fetched_at_iso: new Date(statSync(CACHE_TEXT).mtimeMs).toISOString(),
    bytes: Buffer.byteLength(text, 'utf-8'),
  }
  return { text, meta }
}

function readCacheMeta() {
  try {
    return JSON.parse(readFileSync(CACHE_META, 'utf-8'))
  } catch {
    return null
  }
}

function extractWikipediaTitle(url) {
  try {
    const u = new URL(url)
    if (!/wikipedia\.org$/.test(u.hostname)) return null
    const m = u.pathname.match(/^\/wiki\/(.+)$/)
    if (!m) return null
    return decodeURIComponent(m[1])
  } catch {
    return null
  }
}

export function describeFreshness(meta) {
  if (!meta?.fetched_at_ms) return 'unknown freshness'
  const ageMs = Date.now() - meta.fetched_at_ms
  const ageMin = Math.round(ageMs / 60000)
  if (ageMs < 60_000) return `fetched ${meta.fetched_at_iso} (just now)`
  if (ageMs < ONE_HOUR_MS) return `fetched ${meta.fetched_at_iso} (${ageMin} min ago)`
  const ageHr = Math.round(ageMs / ONE_HOUR_MS)
  return `fetched ${meta.fetched_at_iso} (${ageHr}h ago)`
}
