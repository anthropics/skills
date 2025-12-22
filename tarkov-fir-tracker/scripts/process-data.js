#!/usr/bin/env node
/**
 * Process Tarkov FiR item data from raw sources
 * Creates structured data for the FiR tracker tool
 */

const fs = require('fs');
const path = require('path');

const RAW_DIR = path.join(__dirname, '../data/raw');
const PROCESSED_DIR = path.join(__dirname, '../data/processed');

// Load raw data
const firItems = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'fir_items.json'), 'utf8'));
const firQuests = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'fir_quests.json'), 'utf8'));
const firHideout = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'fir_hideout.json'), 'utf8'));

// Process items: calculate total FiR requirements
const itemSummary = {};

for (const [itemId, itemData] of Object.entries(firItems)) {
  const questRequirements = itemData.quest || {};
  const totalQuestCount = Object.values(questRequirements).reduce((sum, count) => sum + count, 0);

  if (totalQuestCount > 0) {
    itemSummary[itemId] = {
      name: itemData.name?.en || itemId,
      nameShort: itemData.nameShort?.en || itemData.name?.en || itemId,
      type: itemData.type || 'Unknown',
      totalRequired: totalQuestCount,
      questBreakdown: Object.entries(questRequirements).map(([questId, count]) => ({
        questId,
        questName: firQuests[questId]?.name?.en || questId,
        count,
        dealer: firQuests[questId]?.dealer || 'Unknown',
        kappa: firQuests[questId]?.kappa || false
      })),
      canCraft: !!itemData.craft,
      craftLocations: itemData.craft ? Object.keys(itemData.craft) : []
    };
  }
}

// Sort by total required (descending)
const sortedItems = Object.entries(itemSummary)
  .sort((a, b) => b[1].totalRequired - a[1].totalRequired);

// Create final processed data
const processedData = {
  metadata: {
    generatedAt: new Date().toISOString(),
    source: 'fakundo/tarkov-raid-items + TarkovTracker/tarkovdata',
    totalUniqueItems: sortedItems.length,
    totalItemsNeeded: sortedItems.reduce((sum, [, item]) => sum + item.totalRequired, 0)
  },
  items: Object.fromEntries(sortedItems),
  quests: firQuests,
  hideoutStations: firHideout
};

// Write processed data
fs.mkdirSync(PROCESSED_DIR, { recursive: true });
fs.writeFileSync(
  path.join(PROCESSED_DIR, 'fir-requirements.json'),
  JSON.stringify(processedData, null, 2)
);

// Create a simple summary for quick reference
const quickSummary = sortedItems.map(([id, item]) => ({
  id,
  name: item.name,
  total: item.totalRequired,
  type: item.type,
  canCraft: item.canCraft
}));

fs.writeFileSync(
  path.join(PROCESSED_DIR, 'fir-summary.json'),
  JSON.stringify(quickSummary, null, 2)
);

console.log('=== Tarkov FiR Data Processing Complete ===');
console.log(`Total unique FiR items: ${processedData.metadata.totalUniqueItems}`);
console.log(`Total items needed: ${processedData.metadata.totalItemsNeeded}`);
console.log(`\nTop 10 most needed items:`);
sortedItems.slice(0, 10).forEach(([id, item], i) => {
  console.log(`  ${i + 1}. ${item.name}: ${item.totalRequired}x`);
});
