// Validator core. Hardcoded augmentation set + the live-fetched Wikipedia
// catalog get merged into a single rule set per invocation.
//
// The hardcoded set covers items the Wikipedia article doesn't yet
// enumerate but that are unambiguous AI tells in cold-outbound copy
// (modern SaaS-pitch vocab, canned email openers/closers). It exists so
// the validator remains useful even if Wikipedia is unreachable.

const HARDCODED_WORDS = [
  // SaaS / pitch vocabulary that screams "AI generated"
  'leverage', 'leverages', 'leveraging',
  'streamline', 'streamlines', 'streamlining', 'streamlined',
  'transformative', 'transformational',
  'groundbreaking',
  'cutting-edge',
  'seamless', 'seamlessly',
  'elevate', 'elevates', 'elevating',
  'unlock', 'unlocks', 'unlocking',
  'empower', 'empowers', 'empowering',
  'revolutionize', 'revolutionizes', 'revolutionary',
  'paradigm',
  'synergy', 'synergies',
  'holistic', 'holistically',
  // Wikipedia-list items (kept as a baseline in case parser drops them)
  'delve', 'delving',
  'tapestry',
  'meticulous', 'meticulously',
  'pivotal',
  'robust',
  'underscore', 'underscores', 'underscoring',
  'showcase', 'showcases', 'showcasing',
  'testament',
  'intricate', 'intricacies',
  'enduring',
  'fostering', 'foster', 'fostered',
  'garner',
  'bolster', 'bolstered',
  'interplay',
]

const HARDCODED_PHRASES = [
  'i hope this email finds you well',
  'i hope this finds you well',
  'i hope you are doing well',
  'i hope all is well',
  'just checking in',
  'circling back',
  'touching base',
  'wanted to reach out',
  'reaching out to',
  'i wanted to follow up',
  'in conclusion',
  'in summary',
  'to summarize',
  'it is important to note',
  "it's important to note",
  'it is worth noting',
  "it's worth noting",
  'needless to say',
  'at the end of the day',
  "in today's fast-paced",
  "in today's rapidly evolving",
  "in today's digital age",
  "in today's competitive landscape",
  'a wealth of',
  'a treasure trove',
  'a deep dive',
  'plays a vital role',
  'plays a crucial role',
  'plays a pivotal role',
  'plays a key role',
  'plays an important role',
  'plays a significant role',
  'navigate the complexities',
  'navigating the complexities',
  'in the world of',
  'in the realm of',
  'when it comes to',
  'at its core',
  'at its heart',
  'the heart of',
  'a powerful tool',
  'powerful tools',
  'cutting through the noise',
  'move the needle',
  'low-hanging fruit',
  'best-in-class',
  'world-class',
  'next-generation',
  'mission-critical',
  'value proposition',
  'value-add',
  'thought leader',
  'thought leadership',
  'as a leader',
  'as a leading',
  'industry-leading',
  'best practices',
  'enhance your',
  'optimize your',
  'maximize your',
  'unlock your',
  'unlock the power',
  'harness the power',
  'levels up',
  'level up',
  'food for thought',
  'i hope this helps',
  'hope this helps',
  'happy to chat',
  'happy to connect',
  'open to chatting',
  'sounds good',
  'let me know your thoughts',
  'let me know what you think',
  'looking forward to hearing',
  'forward to hearing from you',
]

// Pattern regexes — not derived from Wikipedia, but generally recognized
// AI tells. Each fires on the first match; we don't need every example,
// just the existence of a violation.
const NEGATIVE_PARALLELISM_RE = new RegExp(
  [
    String.raw`\bnot\s+(?:just\s+|merely\s+|simply\s+|only\s+)?[a-z][a-z\s,'-]{2,60}?,?\s+but\s+(?:also\s+|rather\s+)?[a-z]`,
    String.raw`\b(?:aren|isn|don|doesn|didn|won|wouldn|can|couldn|haven|hasn)['’]?t\s+[a-z][^.!?]{3,80}?[—,]\s*(?:they|it|we|you|he|she|i)\b`,
  ].join('|'),
  'i',
)
const RULE_OF_THREE_RE = /\b([a-z]{4,15}),\s+([a-z]{4,15}),?\s+and\s+([a-z]{4,15})\b/i
const PARTICIPLE_TAIL_RE =
  /,\s+(?:reinforcing|ensuring|fostering|enabling|driving|empowering|enhancing|cultivating|underscoring|highlighting|reflecting|symbolizing|contributing|allowing|providing|delivering|positioning|representing|signaling|paving|setting)\s+/i
const WHETHER_YOURE_RE = /\bwhether\s+you\s*['’]?\s*re\b/i
const EXCITED_TO_RE = /\bexcited\s+to\b/i
const EM_DASH_RE = /—/g
const SMART_QUOTE_RE = /[“”‘’]/
const THEMATIC_BREAK_RE = /---+/

/**
 * Build a runtime rule set: hardcoded + Wikipedia-derived. Apply --allow
 * suppressions, then return a normalized object.
 */
export function buildRules({ wikiWords = [], wikiPhrases = [], allow = [], maxEmDashes = 1 } = {}) {
  const allowSet = new Set(allow.map((a) => a.toLowerCase()))
  const words = new Set([...HARDCODED_WORDS, ...wikiWords].map((w) => w.toLowerCase()))
  const phrases = new Set([...HARDCODED_PHRASES, ...wikiPhrases].map((p) => p.toLowerCase()))
  return { words, phrases, allowSet, maxEmDashes }
}

/**
 * Find every AI-tell in `text`. Returns an array of findings; empty when
 * the text is clean. Each finding has a stable `tag` so callers can
 * suppress or counter-prompt specific issues.
 */
export function findAiTells(text, rules) {
  if (!text || typeof text !== 'string') return []
  const findings = []
  const lower = text.toLowerCase()

  for (const word of rules.words) {
    const tag = `banned_word:${word}`
    if (rules.allowSet.has(tag)) continue
    const re = new RegExp(`\\b${escapeRegex(word)}\\b`, 'i')
    const m = re.exec(text)
    if (m) findings.push({ tag, quote: clip(text, m.index, m[0].length), category: 'word' })
  }

  for (const phrase of rules.phrases) {
    const tag = `banned_phrase:${phrase}`
    if (rules.allowSet.has(tag)) continue
    const idx = lower.indexOf(phrase)
    if (idx >= 0) findings.push({ tag, quote: clip(text, idx, phrase.length), category: 'phrase' })
  }

  pushPatternFinding(text, findings, rules, NEGATIVE_PARALLELISM_RE, 'pattern:negative_parallelism', 'pattern')
  pushPatternFinding(text, findings, rules, RULE_OF_THREE_RE, 'pattern:rule_of_three', 'pattern')
  pushPatternFinding(text, findings, rules, PARTICIPLE_TAIL_RE, 'pattern:participle_tail', 'pattern')
  pushPatternFinding(text, findings, rules, WHETHER_YOURE_RE, 'pattern:whether_youre', 'pattern')
  pushPatternFinding(text, findings, rules, EXCITED_TO_RE, 'pattern:excited_to', 'pattern')

  const emDashes = text.match(EM_DASH_RE) ?? []
  if (emDashes.length > rules.maxEmDashes && !rules.allowSet.has('punctuation:em_dash_overuse')) {
    findings.push({
      tag: 'punctuation:em_dash_overuse',
      quote: `${emDashes.length} em-dashes (cap ${rules.maxEmDashes})`,
      category: 'punctuation',
    })
  }
  if (SMART_QUOTE_RE.test(text) && !rules.allowSet.has('punctuation:smart_quotes')) {
    findings.push({
      tag: 'punctuation:smart_quotes',
      quote: text.match(SMART_QUOTE_RE)?.[0] ?? '',
      category: 'punctuation',
    })
  }
  if (THEMATIC_BREAK_RE.test(text) && !rules.allowSet.has('structure:thematic_break')) {
    findings.push({
      tag: 'structure:thematic_break',
      quote: text.match(THEMATIC_BREAK_RE)?.[0] ?? '',
      category: 'structure',
    })
  }

  return findings
}

function pushPatternFinding(text, findings, rules, re, tag, category) {
  if (rules.allowSet.has(tag)) return
  const m = re.exec(text)
  if (m) findings.push({ tag, quote: clip(text, m.index, Math.min(m[0].length, 70)), category })
}

function escapeRegex(s) {
  return s.replace(/[.*+?^${}()|[\]\\-]/g, '\\$&')
}

function clip(text, start, len) {
  const a = Math.max(0, start - 20)
  const b = Math.min(text.length, start + len + 20)
  const prefix = a > 0 ? '…' : ''
  const suffix = b < text.length ? '…' : ''
  return `${prefix}${text.slice(a, b).replace(/\s+/g, ' ')}${suffix}`
}

export function wordCount(text) {
  if (!text) return 0
  return (text.match(/\b[\w'’-]+\b/g) ?? []).length
}

export function summarizeRules(rules) {
  return {
    word_count: rules.words.size,
    phrase_count: rules.phrases.size,
    max_em_dashes: rules.maxEmDashes,
    suppressed: [...rules.allowSet],
  }
}
