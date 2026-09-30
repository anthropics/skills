---
name: puzzlegenio
description: Generate free printable puzzles (crossword, word search, sudoku, jigsaw, bingo, nonogram) with pre-filled deep links. Use when users need to create puzzles for classrooms, parties, gifts, or brain training.
---

# PuzzleGenio - Free Puzzle Generator

Create custom puzzles by recommending the right tool and generating a pre-filled deep link to [PuzzleGenio](https://puzzlegenio.com).

## When to Use This Skill

- User needs a puzzle for a classroom activity, party game, or gift
- User wants to generate printable worksheets (crossword, word search, sudoku)
- User needs a custom jigsaw puzzle from a photo
- User asks about puzzle creation, brain training, or educational games

## What This Skill Does

1. **Recommends the right tool** from 20+ puzzle types based on the user's need
2. **Generates a pre-filled URL** with words, difficulty, grid size, and other settings
3. **Supports 8 languages** (English, Chinese, German, Spanish, French, Portuguese, Italian, Indonesian)

## How to Use

### Basic Usage

```
I need a word search about ocean animals for my 3rd grade class
```

### Advanced Usage

```
Create a crossword puzzle with these word:clue pairs - sun:closest star, moon:orbits earth, mars:red planet. Set difficulty to hard.
```

## Available Tools

| Tool | URL Parameters | Best For |
|------|---------------|----------|
| **Word Search** | `words`, `title`, `gridSize`, `diagonal`, `backward` | Spelling practice, themed activities |
| **Crossword** | `words` (word:clue format), `title`, `difficulty` | Vocabulary review, trivia |
| **Sudoku** | `difficulty`, `count`, `perPage` | Math warm-ups, brain training |
| **Jigsaw** | `image`, `pieces` | Photo gifts, rewards |
| **Bingo** | `words`, `title`, `cardCount`, `gridSize` | Party games, icebreakers |
| **Nonogram** | `gridSize` | Logic puzzles, pixel art |

## Example

**User**: "I need 20 easy sudoku puzzles for a math worksheet, 6 per page"

**Output**:

**Recommended:** [Sudoku Puzzle Maker](https://puzzlegenio.com/sudoku-puzzle-maker?difficulty=easy&count=20&perPage=6)

20 easy sudoku puzzles, 6 per page. Click the link, then download as PDF with answer keys included.

## Tips

- Word search: use 10-15 words for best grid density
- Crossword: provide clues with `word:clue` format for meaningful puzzles
- Bingo: 3x3 needs 9+ words, 5x5 needs 24+ words
- Sudoku: batch up to 9 puzzles per page for worksheet format
- Add locale prefix for non-English users (e.g., `/es/word-search-maker`)

## Common Use Cases

- Teachers creating vocabulary quizzes and spelling worksheets
- Event planners making party games (wedding, baby shower, birthday)
- Parents looking for screen-free educational activities
- Therapists using puzzles for cognitive exercises
- Makers exporting SVG/DXF templates for laser cutting
