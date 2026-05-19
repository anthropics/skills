import { test } from 'node:test'
import { strict as assert } from 'node:assert'
import { buildRules, findAiTells, wordCount } from '../lib/validator.mjs'
import { parseSignsArticle } from '../lib/wikiParser.mjs'

// Default rules: maxEmDashes=0, requireProperCaps=true. Tests that need
// the old laxer behavior pass overrides explicitly.
const rules = buildRules({ wikiWords: [], wikiPhrases: [] })

test('clean human-sounding text passes', () => {
  const f = findAiTells(
    'Hey Adam, your workshop on BPO strategy got me thinking. When teams pull headcount out of fraud review, the audit trail breaks first. Worth a quick call?',
    rules,
  )
  assert.equal(f.length, 0)
})

test('banned word: delve fires', () => {
  const tags = findAiTells('We delve into this problem.', rules).map((x) => x.tag)
  assert.ok(tags.includes('banned_word:delve'))
})

test('banned phrase: circling back fires', () => {
  const tags = findAiTells('Just circling back on my note.', rules).map((x) => x.tag)
  assert.ok(tags.includes('banned_phrase:circling back'))
})

test('negative parallelism: Not X but Y', () => {
  const tags = findAiTells('Not a fraud model, but a governance layer.', rules).map((x) => x.tag)
  assert.ok(tags.includes('pattern:negative_parallelism'))
})

test('contracted negative parallelism: aren\'t X — they\'re Y', () => {
  // Use a comma separator to avoid double-triggering the em-dash rule
  // alongside the parallelism rule — we only want the parallelism finding.
  const tags = findAiTells(
    "The teams closing this gap aren't hiring more reviewers, they're making AI inspectable.",
    rules,
  ).map((x) => x.tag)
  assert.ok(tags.includes('pattern:negative_parallelism'))
})

test('rule of three: a, b, and c', () => {
  const tags = findAiTells('Clear, sourced, and trustworthy outputs', rules).map((x) => x.tag)
  assert.ok(tags.includes('pattern:rule_of_three'))
})

test('participle tail: , ensuring X', () => {
  const tags = findAiTells('We build review tooling, ensuring auditor trust.', rules).map((x) => x.tag)
  assert.ok(tags.includes('pattern:participle_tail'))
})

test('any em-dash fails at default (maxEmDashes=0)', () => {
  const tags = findAiTells("It's Artemii — quick question for you.", rules).map((x) => x.tag)
  assert.ok(tags.includes('punctuation:em_dash'))
})

test('one em-dash is allowed when maxEmDashes=1', () => {
  const lax = buildRules({ maxEmDashes: 1 })
  const tags = findAiTells("It's Artemii — quick question for you.", lax).map((x) => x.tag)
  assert.ok(!tags.includes('punctuation:em_dash'))
  assert.ok(!tags.includes('punctuation:em_dash_overuse'))
})

test('two em-dashes fire em_dash_overuse at maxEmDashes=1', () => {
  const lax = buildRules({ maxEmDashes: 1 })
  const tags = findAiTells('Alpha — beta — gamma', lax).map((x) => x.tag)
  assert.ok(tags.includes('punctuation:em_dash_overuse'))
})

test('sentence-start lowercase fires when requireProperCaps=true', () => {
  const tags = findAiTells('Hey Matt. your session got me thinking.', rules).map((x) => x.tag)
  assert.ok(tags.includes('caps:sentence_start_lowercase'))
})

test('first-character lowercase fires', () => {
  const tags = findAiTells('hey Matt, quick question.', rules).map((x) => x.tag)
  assert.ok(tags.includes('caps:sentence_start_lowercase'))
})

test('lowercase pronoun "i" fires', () => {
  const tags = findAiTells('Hey Matt, i wanted to ask one question.', rules).map((x) => x.tag)
  assert.ok(tags.includes('caps:pronoun_i_lowercase'))
})

test('requireProperCaps=false skips caps checks', () => {
  const lax = buildRules({ requireProperCaps: false })
  const tags = findAiTells('hey matt, i wanted to ask one question.', lax).map((x) => x.tag)
  assert.ok(!tags.includes('caps:sentence_start_lowercase'))
  assert.ok(!tags.includes('caps:pronoun_i_lowercase'))
})

test('smart quotes flag', () => {
  const tags = findAiTells('The “review queue” problem.', rules).map((x) => x.tag)
  assert.ok(tags.includes('punctuation:smart_quotes'))
})

test('--allow suppresses a specific tag', () => {
  const r = buildRules({ allow: ['banned_word:delve'] })
  const tags = findAiTells('We delve into this problem.', r).map((x) => x.tag)
  assert.ok(!tags.includes('banned_word:delve'))
})

test('wordCount handles punctuation, contractions, hyphenation', () => {
  assert.equal(wordCount("hey, it's a 5-word touch."), 5)
  assert.equal(wordCount(''), 0)
})

test('parseSignsArticle extracts bulleted words under known headings', () => {
  // Minimal synthetic wikitext that mimics the structure of the real
  // article. We don't ship a real fixture to avoid bloating the repo;
  // this validates the parser still handles a representative shape.
  const wikitext = [
    '== Overused words ==',
    'Some intro text.',
    '* delve',
    "* tapestry — '''abstract''' usage",
    '* meticulous',
    '* an entire sentence that should be ignored because it is way too long to be a lemma',
    '== Unrelated section ==',
    '* ignored item',
    '== Common phrases ==',
    '* I hope this email finds you well',
    '* circling back',
  ].join('\n')
  const { words, phrases } = parseSignsArticle(wikitext)
  assert.ok(words.includes('delve'))
  assert.ok(words.includes('tapestry'))
  assert.ok(words.includes('meticulous'))
  assert.ok(!words.includes('ignored'), '"ignored item" was under an unrelated heading')
  assert.ok(phrases.includes('i hope this email finds you well'))
  assert.ok(phrases.includes('circling back'))
})
