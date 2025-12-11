#!/bin/bash

# MarkLogic Flux Reprocess Wrapper Script
# Usage: ./flux-reprocess.sh <read-js-file> <write-js-file>

set -e

READ_JS_FILE=${1:?Read JavaScript file required}
WRITE_JS_FILE=${2:?Write JavaScript file required}

# Get configuration from environment or use defaults
ML_HOST=${ML_HOST:-localhost}
ML_PORT=${ML_PORT:-8004}
ML_USER=${ML_USER:-admin}
ML_PASS=${ML_PASS:-admin}
BATCH_SIZE=${BATCH_SIZE:-100}
THREAD_COUNT=${THREAD_COUNT:-32}

CONNECTION="${ML_USER}:${ML_PASS}@${ML_HOST}:${ML_PORT}"

echo "========================================="
echo "MarkLogic Flux Reprocess"
echo "========================================="
echo "Read JS:  ${READ_JS_FILE}"
echo "Write JS: ${WRITE_JS_FILE}"
echo "Target:   ${ML_HOST}:${ML_PORT}"
echo "Batch:    ${BATCH_SIZE}"
echo "Threads:  ${THREAD_COUNT}"
echo "========================================="

# Check files exist
if [ ! -f "${READ_JS_FILE}" ]; then
    echo "ERROR: Read JavaScript file not found: ${READ_JS_FILE}"
    exit 1
fi

if [ ! -f "${WRITE_JS_FILE}" ]; then
    echo "ERROR: Write JavaScript file not found: ${WRITE_JS_FILE}"
    exit 1
fi

# Read file contents
READ_JS=$(cat "${READ_JS_FILE}")
WRITE_JS=$(cat "${WRITE_JS_FILE}")

echo ""
echo "Starting reprocess..."
flux reprocess \
    --connection-string "${CONNECTION}" \
    --read-javascript "${READ_JS}" \
    --write-javascript "${WRITE_JS}" \
    --batch-size ${BATCH_SIZE} \
    --thread-count ${THREAD_COUNT} \
    --log-progress 10000

echo ""
echo "========================================="
echo "Reprocess completed successfully!"
echo "========================================="
