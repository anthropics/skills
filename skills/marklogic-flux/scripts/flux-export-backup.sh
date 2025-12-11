#!/bin/bash

# MarkLogic Flux Export Backup Script
# Usage: ./flux-export-backup.sh <collection-name> [output-dir]

set -e

COLLECTION=${1:?Collection name required}
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_DIR=${2:-backup/${COLLECTION}_${TIMESTAMP}}

# Get configuration from environment or use defaults
ML_HOST=${ML_HOST:-localhost}
ML_PORT=${ML_PORT:-8004}
ML_USER=${ML_USER:-admin}
ML_PASS=${ML_PASS:-admin}

CONNECTION="${ML_USER}:${ML_PASS}@${ML_HOST}:${ML_PORT}"

echo "========================================="
echo "MarkLogic Flux Export Backup"
echo "========================================="
echo "Collection:  ${COLLECTION}"
echo "Output Dir:  ${OUTPUT_DIR}"
echo "Source:      ${ML_HOST}:${ML_PORT}"
echo "Timestamp:   ${TIMESTAMP}"
echo "========================================="

# Create output directory
mkdir -p "${OUTPUT_DIR}"

# Count documents first
echo ""
echo "Counting documents..."
DOC_COUNT=$(flux export-files \
    --connection-string "${CONNECTION}" \
    --collections "${COLLECTION}" \
    --count 2>&1 | grep "Total" | awk '{print $2}')

echo "Documents to export: ${DOC_COUNT}"
echo ""

# Export with compression
echo "Starting export..."
flux export-files \
    --connection-string "${CONNECTION}" \
    --collections "${COLLECTION}" \
    --path "${OUTPUT_DIR}" \
    --compression zip \
    --zip-file-count 1 \
    --thread-count 32 \
    --log-progress 10000

echo ""
echo "========================================="
echo "Backup completed successfully!"
echo "Location: ${OUTPUT_DIR}"
echo "Documents: ${DOC_COUNT}"
echo "========================================="

# Show backup size
if [ -d "${OUTPUT_DIR}" ]; then
    du -sh "${OUTPUT_DIR}"
fi
