#!/bin/bash

# MarkLogic Flux Import Wrapper Script
# Usage: ./flux-import.sh <collection-name> <file-path>

set -e

COLLECTION=${1:?Collection name required}
FILE_PATH=${2:?File path required}

# Get configuration from environment or use defaults
ML_HOST=${ML_HOST:-localhost}
ML_PORT=${ML_PORT:-8004}
ML_USER=${ML_USER:-admin}
ML_PASS=${ML_PASS:-admin}

CONNECTION="${ML_USER}:${ML_PASS}@${ML_HOST}:${ML_PORT}"

echo "========================================="
echo "MarkLogic Flux Import"
echo "========================================="
echo "Collection: ${COLLECTION}"
echo "File Path:  ${FILE_PATH}"
echo "Target:     ${ML_HOST}:${ML_PORT}"
echo "========================================="

# Detect file type
FILE_EXT="${FILE_PATH##*.}"

case "$FILE_EXT" in
  csv|tsv)
    CMD="import-delimited-files"
    ;;
  json|jsonl)
    CMD="import-json-files"
    ;;
  xml)
    CMD="import-xml-files"
    ;;
  parquet)
    CMD="import-parquet-files"
    ;;
  *)
    CMD="import-files"
    ;;
esac

echo "Using command: flux ${CMD}"
echo ""

flux ${CMD} \
    --connection-string "${CONNECTION}" \
    --path "${FILE_PATH}" \
    --collections "${COLLECTION}" \
    --permissions "rest-reader,read,rest-writer,update" \
    --batch-size 100 \
    --thread-count 32 \
    --log-progress 10000

echo ""
echo "========================================="
echo "Import completed successfully!"
echo "========================================="
