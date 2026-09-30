#!/bin/bash
# auto-roadmap.sh - Autopilot: lancia sessioni Claude Code in loop
# Ogni sessione = contesto fresco (come premere Cmd+N)
# Si ferma quando la roadmap è completata o se Claude si blocca
#
# Usage: ./auto-roadmap.sh [path-to-claude-md] [max-sessions]
# Example: ./auto-roadmap.sh CLAUDE.md 20

set -e

CLAUDE_MD="${1:-CLAUDE.md}"
MAX_SESSIONS="${2:-50}"
SESSION_COUNT=0
STUCK_COUNT=0
MAX_STUCK=3

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}╔══════════════════════════════════════╗${NC}"
echo -e "${BLUE}║     ROADMAP PILOT - AUTO MODE        ║${NC}"
echo -e "${BLUE}╚══════════════════════════════════════╝${NC}"
echo ""

# Verify CLAUDE.md exists
if [ ! -f "$CLAUDE_MD" ]; then
  echo -e "${RED}ERROR: $CLAUDE_MD not found${NC}"
  echo "Create a CLAUDE.md with a ## Roadmap section first."
  exit 1
fi

# Verify claude CLI is available
if ! command -v claude &> /dev/null; then
  echo -e "${RED}ERROR: 'claude' CLI not found${NC}"
  echo "Install Claude Code first: https://docs.anthropic.com/en/docs/claude-code"
  exit 1
fi

# Count initial state
TOTAL=$(grep -c '^\- \[.\]' "$CLAUDE_MD" 2>/dev/null || echo 0)
DONE_INITIAL=$(grep -c '^\- \[x\]' "$CLAUDE_MD" 2>/dev/null || echo 0)
REMAINING=$((TOTAL - DONE_INITIAL))

echo -e "${YELLOW}Roadmap: ${DONE_INITIAL}/${TOTAL} completati, ${REMAINING} rimanenti${NC}"
echo -e "${YELLOW}Max sessioni: ${MAX_SESSIONS}${NC}"
echo ""

if [ "$REMAINING" -eq 0 ]; then
  echo -e "${GREEN}Roadmap gia' completata! Nessun task rimasto.${NC}"
  exit 0
fi

# Main loop
while [ "$SESSION_COUNT" -lt "$MAX_SESSIONS" ]; do
  # Check remaining tasks
  REMAINING_NOW=$(grep -c '^\- \[ \]' "$CLAUDE_MD" 2>/dev/null || echo 0)

  if [ "$REMAINING_NOW" -eq 0 ]; then
    echo ""
    echo -e "${GREEN}╔══════════════════════════════════════╗${NC}"
    echo -e "${GREEN}║     ROADMAP COMPLETATA!              ║${NC}"
    echo -e "${GREEN}╚══════════════════════════════════════╝${NC}"
    echo ""
    echo -e "${GREEN}Sessioni usate: ${SESSION_COUNT}${NC}"
    echo -e "${GREEN}Task completati: ${TOTAL}/${TOTAL}${NC}"
    exit 0
  fi

  SESSION_COUNT=$((SESSION_COUNT + 1))
  DONE_BEFORE=$(grep -c '^\- \[x\]' "$CLAUDE_MD" 2>/dev/null || echo 0)

  # Show current task
  NEXT_TASK=$(grep '^\- \[ \]' "$CLAUDE_MD" | head -1 | sed 's/^- \[ \] //')
  echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
  echo -e "${BLUE}Sessione #${SESSION_COUNT}/${MAX_SESSIONS}${NC}"
  echo -e "${YELLOW}Prossimo task: ${NEXT_TASK}${NC}"
  echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"

  # Launch Claude Code as a fresh session
  claude -p "Leggi il file CLAUDE.md e esegui il prossimo task non completato dalla roadmap. Segui le istruzioni della skill roadmap-pilot: esegui UN solo task, spuntalo, committa, e fermati. Non pushare." \
    --max-turns 25 \
    2>&1 | while IFS= read -r line; do
      echo "  $line"
    done

  # Check if progress was made
  DONE_AFTER=$(grep -c '^\- \[x\]' "$CLAUDE_MD" 2>/dev/null || echo 0)

  if [ "$DONE_AFTER" -gt "$DONE_BEFORE" ]; then
    STUCK_COUNT=0
    echo -e "${GREEN}Task completato! (${DONE_AFTER}/${TOTAL})${NC}"
  else
    STUCK_COUNT=$((STUCK_COUNT + 1))
    echo -e "${RED}Nessun progresso in questa sessione (tentativo ${STUCK_COUNT}/${MAX_STUCK})${NC}"

    if [ "$STUCK_COUNT" -ge "$MAX_STUCK" ]; then
      echo ""
      echo -e "${RED}╔══════════════════════════════════════╗${NC}"
      echo -e "${RED}║  BLOCCATO: ${MAX_STUCK} sessioni senza progresso  ║${NC}"
      echo -e "${RED}╚══════════════════════════════════════╝${NC}"
      echo ""
      echo -e "${RED}Prossimo task bloccante: ${NEXT_TASK}${NC}"
      echo -e "${YELLOW}Intervieni manualmente e poi rilancia lo script.${NC}"
      exit 2
    fi
  fi

  echo ""
  sleep 2
done

echo ""
echo -e "${YELLOW}Raggiunto il limite di ${MAX_SESSIONS} sessioni.${NC}"
DONE_FINAL=$(grep -c '^\- \[x\]' "$CLAUDE_MD" 2>/dev/null || echo 0)
echo -e "${YELLOW}Progresso: ${DONE_FINAL}/${TOTAL} task completati.${NC}"
exit 1
