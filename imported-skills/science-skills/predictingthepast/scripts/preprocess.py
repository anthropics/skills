# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Preprocess ancient text for Predicting The Past (Aeneas/Ithaca) inference.

Cleans input text to contain only valid alphabet characters for the specified
language (Latin or Greek), following the conventions from the
predictingthepast library. Handles:
  - Lowercasing and accent removal (Greek).
  - Numeral conversion (Arabic digits → '0', Roman numerals → '0').
  - Punctuation removal and editorial bracket stripping.
  - Preservation of restoration markers (?, #) and special chars (-, _, .).
  - Input validation (minimum length, marker constraints).
"""

# /// script
# requires-python = ">=3.10"
# ///

import argparse
import re
import sys
import unicodedata

GREEK_ALPHABET: list[str] = list('αβγδεζηθικλμνξοπρςστυφχψωϛ')
# Classical Latin alphabet — J and W are post-classical additions, not used
# by the predictingthepast model vocabulary (see LatinAlphabet in the library).
LATIN_ALPHABET: list[str] = list('abcdefghiklmnopqrstuvxyz')

SPECIAL_CHARS: list[str] = [' ', '-', '_', '.', '?', '#', '0']

MIN_LEN: int = 25


def strip_accents(text: str) -> str:
  """Remove combining diacritical marks (accents) from Greek text.

  Uses Unicode NFD decomposition to separate base letters from combining
  marks, then filters out the marks (category 'Mn').

  Args:
      text: Input text potentially containing accented characters.

  Returns:
      Text with all combining marks removed.
  """
  return ''.join(
      c
      for c in unicodedata.normalize('NFD', text)
      if unicodedata.category(c) != 'Mn'
  )


def numerals_to_zero(text: str) -> str:
  """Replace Arabic digits and Roman numerals with '0' in Latin text.

  Arabic digits: any sequence of [0-9] becomes a single '0'.
  Roman numerals: word-boundary-delimited sequences of m/d/c/l/x/v/i
  are replaced with '0'. Empty matches are skipped.

  Args:
      text: Input Latin text.

  Returns:
      Text with numerals replaced by '0'.
  """
  text = re.sub(r'[0-9]+', '0', text)
  text = re.sub(
      r'\b(m{0,3})(cm|cd|d?c{0,3})(xc|xl|l?x{0,3})(ix|iv|v?i{0,3})\b',
      lambda m: '0' if m.group(0) else m.group(0),
      text,
  )
  return text


def greek_numerals_to_zero(text: str) -> str:
  """Replace Arabic digit sequences with '0' in Greek text.

  Greek numeral notation (e.g. αʹ, βʹ) is handled during accent stripping
  and alphabet filtering. This function only normalizes Arabic digits.

  Args:
      text: Input Greek text.

  Returns:
      Text with Arabic digit sequences replaced by '0'.
  """
  text = re.sub(r'[0-9]+', '0', text)
  return text


def validate_restoration_markers(text: str) -> list[str]:
  """Check that restoration markers (? and #) follow the required rules.

  Rules:
    - No consecutive '##' (use a single # per unknown-length gap).
    - No adjacent '?#' or '#?' (unknown-length must not abut fixed-length).

  Args:
      text: Preprocessed text containing restoration markers.

  Returns:
      List of error messages. Empty if all markers are valid.
  """
  errors = []

  if '##' in text:
    errors.append('Consecutive ## found. Use a single # per unknown-length gap')

  if '?#' in text or '#?' in text:
    errors.append(
        'Adjacent ?# or #? found. Unknown-length # must not be '
        'adjacent to fixed-length ?'
    )

  return errors


def preprocess_latin(text: str) -> str:
  """Clean Latin epigraphic text for Aeneas inference.

  Processing pipeline:
    1. Lowercase the entire text.
    2. Convert Arabic digits and Roman numerals to '0'.
    3. Strip punctuation (!, comma, semicolon, middle dot).
    4. Remove editorial brackets ([...], (...)) keeping their contents.
    5. Filter to valid Latin alphabet + special characters.
    6. Collapse whitespace.

  Args:
      text: Raw Latin inscription text.

  Returns:
      Cleaned text containing only valid characters.
  """
  text = text.replace('\\n', ' ').replace('\n', ' ')

  text = text.lower()

  text = numerals_to_zero(text)

  text = re.sub(r'[!,;\xb7]', '', text)

  text = re.sub(r'\[([^\]]*)\]', r'\1', text)
  text = re.sub(r'\(([^\)]*)\)', r'\1', text)
  text = re.sub(r'<([^>]*)>', r'\1', text)

  valid = set(LATIN_ALPHABET + SPECIAL_CHARS)
  text = ''.join(c if c in valid else ' ' for c in text)

  text = re.sub(r'\s+', ' ', text).strip()
  return text


def preprocess_greek(text: str) -> str:
  """Clean Greek epigraphic text for Ithaca inference.

  Processing pipeline:
    1. Lowercase the entire text.
    2. Remove combining diacritical marks (accents).
    3. Convert Arabic digit sequences to '0'.
    4. Normalize lunate sigma (ϲ → σ).
    5. Normalize double brackets (〚/〛 → [/]).
    6. Strip angle-bracket editorial additions (<...>) keeping contents.
    7. Remove curly-bracket editorial comments ({...}).
    8. Remove parenthetical annotations ((...)).
    9. Normalize em-dashes and en-dashes to hyphens.
   10. Preserve multi-dash sequences (editorial lacunae).
   11. Filter to valid Greek alphabet + special characters.
   12. Collapse whitespace.

  Args:
      text: Raw Greek inscription text.

  Returns:
      Cleaned text containing only valid characters.
  """
  text = text.replace('\\n', ' ').replace('\n', ' ')

  text = text.lower()

  text = strip_accents(text)

  text = greek_numerals_to_zero(text)

  text = text.replace('ϲ', 'σ')

  text = re.sub(r'〚', '[', text)
  text = re.sub(r'〛', ']', text)

  text = re.sub(r'\[([^\]]*)\]', r'\1', text)
  text = re.sub(r'\(([^\)]*)\)', r'\1', text)
  text = re.sub(r'<([^>]*)>', r'\1', text)

  text = re.sub(r'{[^}]*}', '', text)

  text = re.sub(r'[;·\xb7]', '.', text)

  text = text.replace('\u2013', '-')
  text = text.replace('\u2014', '-')
  text = text.replace('—', '-')

  text = re.sub(r'---+', lambda m: '-' * len(m.group(0)), text)

  valid = set(GREEK_ALPHABET + SPECIAL_CHARS)
  text = ''.join(c if c in valid else ' ' for c in text)

  text = re.sub(r'\s+', ' ', text).strip()
  return text


def main() -> None:
  """Entry point: parse arguments, preprocess text, and validate output."""
  parser = argparse.ArgumentParser(
      description='Preprocess text for Predicting The Past inference.'
  )
  parser.add_argument(
      '--language',
      required=True,
      choices=['latin', 'greek'],
      help='Language of the input text.',
  )
  input_group = parser.add_mutually_exclusive_group(required=True)
  input_group.add_argument('--input', help='Input text string.')
  input_group.add_argument('--input_file', help='Path to input text file.')
  parser.add_argument('--output_file', help='Path to save cleaned text.')

  args = parser.parse_args()

  if args.input:
    text = args.input
  else:
    with open(args.input_file, 'r', encoding='utf-8') as f:
      text = f.read()

  if args.language == 'latin':
    cleaned = preprocess_latin(text)
  else:
    cleaned = preprocess_greek(text)

  if len(cleaned) < MIN_LEN:
    print(
        f'WARNING: Text is {len(cleaned)} chars '
        f'(minimum {MIN_LEN}). Pad with dashes (-) to '
        f'reach at least {MIN_LEN} chars.',
        file=sys.stderr,
    )

  marker_errors = validate_restoration_markers(cleaned)
  for err in marker_errors:
    print(f'WARNING: {err}', file=sys.stderr)

  if args.output_file:
    with open(args.output_file, 'w', encoding='utf-8') as f:
      f.write(cleaned)
    print(f'Cleaned text written to {args.output_file}')
    print(f'Length: {len(cleaned)} characters')
  else:
    print(cleaned)
    print(f'\n--- Length: {len(cleaned)} characters ---', file=sys.stderr)


if __name__ == '__main__':
  main()
