// Parses the wikitext of `Wikipedia:Signs_of_AI_writing` into a structured
// rule set the validator can consume. The article is community-edited so
// new tells appear over time; this parser is intentionally forgiving —
// it pulls every bulleted item under specific headings and lets the
// validator's category logic decide how to apply each entry.
//
// We extract:
//   - Words and short phrases (≤4 tokens) under "AI vocabulary" type sections.
//   - Multi-word phrases (≥5 tokens) treated as banned phrases.
//   - Pattern hints under sections naming "parallelism", "rule of three", etc.
//
// Anything we can't parse cleanly is ignored — the hardcoded validator
// rules backstop the coverage. This is a "best effort + augment" parser,
// not an authoritative one.

const WIKILINK_RE = /\[\[(?:[^\]|]*\|)?([^\]]+)\]\]/g
const TEMPLATE_RE = /\{\{[^}]*\}\}/g
const REF_RE = /<ref[^>]*>[\s\S]*?<\/ref>|<ref[^/]*\/>/g
const BOLD_RE = /'''([^']+)'''/g
const ITALIC_RE = /''([^']+)''/g
const CURLY_QUOTES_RE = /[“”‘’]/g

// Headings (case-insensitive substring) under which we treat bulleted
// items as banned vocabulary / phrases. The Wikipedia article moves
// content around; this is a forgiving list.
const VOCAB_HEADINGS = [
  'overused words',
  'overused phrases',
  'ai vocabulary',
  'puffery',
  'significance',
  'promotional',
  'words and phrases',
  'characteristic words',
  'common phrases',
  'phrases',
  'tropes',
]

export function parseSignsArticle(wikitext) {
  const sections = splitSections(wikitext)
  const words = new Set()
  const phrases = new Set()

  for (const section of sections) {
    const headingLower = section.heading.toLowerCase()
    const matched = VOCAB_HEADINGS.some((h) => headingLower.includes(h))
    if (!matched) continue
    for (const item of extractBulletItems(section.body)) {
      const cleaned = cleanItem(item)
      if (!cleaned) continue
      const tokens = cleaned.split(/\s+/)
      if (tokens.length <= 1) {
        words.add(tokens[0].toLowerCase())
      } else if (tokens.length <= 4) {
        // Short fragments: treat each as a phrase (substring match).
        phrases.add(cleaned.toLowerCase())
      } else {
        phrases.add(cleaned.toLowerCase())
      }
    }
  }

  return {
    words: [...words].filter((w) => w.length >= 3 && !/^[^a-z]+$/.test(w)),
    phrases: [...phrases].filter((p) => p.length >= 4),
  }
}

function splitSections(wikitext) {
  // Wikipedia headings: ==Top==, ===Sub===, ====Subsub====
  const lines = wikitext.split(/\r?\n/)
  const sections = []
  let current = { heading: '__root__', level: 0, body: '' }
  for (const line of lines) {
    const headingMatch = line.match(/^(={2,6})\s*(.+?)\s*\1\s*$/)
    if (headingMatch) {
      sections.push(current)
      current = { heading: headingMatch[2], level: headingMatch[1].length, body: '' }
      continue
    }
    current.body += line + '\n'
  }
  sections.push(current)
  return sections
}

function extractBulletItems(body) {
  // Bullet lines start with one or more `*` or `#`. Multi-line continuation
  // (a bullet that wraps onto the next line) is rare in the article —
  // tolerate but don't require.
  const items = []
  let buffer = ''
  for (const line of body.split(/\r?\n/)) {
    const m = line.match(/^[*#:]+\s*(.*)$/)
    if (m) {
      if (buffer) items.push(buffer)
      buffer = m[1]
    } else if (buffer && line.trim()) {
      // Continuation of the previous bullet — but only if it doesn't look
      // like a new structural element.
      if (!/^[=|{]/.test(line.trim())) {
        buffer += ' ' + line.trim()
      }
    } else if (buffer) {
      items.push(buffer)
      buffer = ''
    }
  }
  if (buffer) items.push(buffer)
  return items
}

function cleanItem(raw) {
  let s = raw
  // Strip refs first (they often contain templates).
  s = s.replace(REF_RE, '')
  // Strip templates.
  s = s.replace(TEMPLATE_RE, '')
  // Pull display text out of wikilinks.
  s = s.replace(WIKILINK_RE, (_, txt) => txt)
  // Strip bold / italic markers.
  s = s.replace(BOLD_RE, '$1').replace(ITALIC_RE, '$1')
  // Convert curly quotes to straight.
  s = s.replace(CURLY_QUOTES_RE, '"')
  // Trim leading punctuation/colons that look like "Word: explanation".
  // Take only the head before the first colon or em-dash — that's the
  // "lemma" we care about.
  const head = s.split(/[:—–]/)[0] ?? s
  // Strip surrounding quotes.
  let cleaned = head.replace(/^["'`]+|["'`]+$/g, '').trim()
  // Drop trailing commas / periods.
  cleaned = cleaned.replace(/[,.;]$/, '').trim()
  // Reject if it still contains template artifacts.
  if (/[{}<>|]/.test(cleaned)) return null
  // Reject overlong "lemmas" — likely an entire sentence the parser failed
  // to split. The catalog is single words and short fragments.
  if (cleaned.length > 60) return null
  // Reject if it contains digits or non-alpha noise.
  if (/[0-9]/.test(cleaned)) return null
  // Lowercase for matching.
  return cleaned.toLowerCase()
}
