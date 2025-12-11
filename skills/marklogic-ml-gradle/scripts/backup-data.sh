#!/bin/bash
# Export/backup MarkLogic data with timestamp
# Usage: ./scripts/backup-data.sh [--include-modules] [--include-schemas]

set -e

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BACKUP_DIR="backup/$TIMESTAMP"
INCLUDE_MODULES=false
INCLUDE_SCHEMAS=false

while [[ $# -gt 0 ]]; do
  case $1 in
    --include-modules)
      INCLUDE_MODULES=true
      shift
      ;;
    --include-schemas)
      INCLUDE_SCHEMAS=true
      shift
      ;;
    *)
      echo "Unknown option: $1"
      echo "Usage: $0 [--include-modules] [--include-schemas]"
      exit 1
      ;;
  esac
done

echo "💾 Backing up MarkLogic data..."
echo "==============================="
echo "Backup directory: $BACKUP_DIR"
echo ""

# Create backup directory
mkdir -p "$BACKUP_DIR"

# Export data
echo "📦 Exporting data..."
gradle mlExport -PexportDir="$BACKUP_DIR/data"

# Export modules if requested
if [ "$INCLUDE_MODULES" = true ]; then
  echo "📦 Exporting modules..."
  gradle mlExportModules -PexportDir="$BACKUP_DIR/modules"
fi

# Export schemas if requested
if [ "$INCLUDE_SCHEMAS" = true ]; then
  echo "📦 Exporting schemas..."
  gradle mlExportSchemas -PexportDir="$BACKUP_DIR/schemas"
fi

echo ""
echo "==============================="
echo "✅ Backup complete: $BACKUP_DIR"
echo ""
echo "To restore:"
echo "  gradle mlLoadData -PdataDir=$BACKUP_DIR/data"
if [ "$INCLUDE_MODULES" = true ]; then
  echo "  gradle mlLoadModules -PmodulePaths=$BACKUP_DIR/modules"
fi
