import { test } from 'node:test'
import { strict as assert } from 'node:assert'
import { buildRules, findAiTells, wordCount } from '../lib/validator.mjs'
import { parseSignsArticle } from '../lib/wikiParser.mjs'

const rules = buildRules({ wikiWords: [], wikiPhrases: [], allow: [], maxEmDashes: 1 })

test('clean human-sounding text passes', () => {
  const f = findAiTells(
    'hey adam, your workshop on bpo strategy got me thinking. when teams pull headcount out of fraud review, the audit trail breaks first. worth a quick call?',
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
  const tags = findAiTells(
    "the teams closing this gap aren't hiring more reviewers — they're making AI inspectable.",
    rules,
  ).map((x) => x.tag)
  assert.ok(tags.includes('pattern:negative_parallelism'))
})

test('rule of three: a, b, and c', () => {
  const tags = findAiTells('clear, sourced, and trustworthy outputs', rules).map((x) => x.tag)
  assert.ok(tags.includes('pattern:rule_of_three'))
})

test('participle tail: , ensuring X', () => {
  const tags = findAiTells('We build review tooling, ensuring auditor trust.', rules).map((x) => x.tag)
  assert.ok(tags.includes('pattern:participle_tail'))
})

test('em-dash overuse (≥2)', () => {
  const tags = findAiTells('alpha — beta — gamma', rules).map((x) => x.tag)
  assert.ok(tags.includes('punctuation:em_dash_overuse'))
})

test('one em-dash is allowed at default cap', () => {
  const tags = findAiTells("hey, it's Artemii — quick question for you.", rules).map((x) => x.tag)
  assert.ok(!tags.includes('punctuation:em_dash_overuse'))
})

test('smart quotes flag', () => {
  const tags = findAiTells('the “review queue” problem', rules).map((x) => x.tag)
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
