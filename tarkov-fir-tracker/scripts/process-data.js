#!/usr/bin/env node
/**
 * Process Tarkov FiR item data from raw sources
 * FiR (Found in Raid) items only - for quest requirements
 * Includes quest progression analysis for priority sorting
 */

const fs = require('fs');
const path = require('path');

const RAW_DIR = path.join(__dirname, '../data/raw');
const PROCESSED_DIR = path.join(__dirname, '../data/processed');

// Load raw data
const firItems = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'fir_items.json'), 'utf8'));
const firQuests = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'fir_quests.json'), 'utf8'));
const rawQuests = JSON.parse(fs.readFileSync(path.join(RAW_DIR, 'quests.json'), 'utf8'));

// ============================================
// Quest Progression Analysis
// ============================================

const questById = {};
rawQuests.forEach(q => {
  questById[q.id] = q;
});

function calculateQuestDepth(questId, visited = new Set()) {
  if (visited.has(questId)) return 0;
  visited.add(questId);

  const quest = questById[questId];
  if (!quest) return 0;

  const prereqs = quest.require?.quests || [];
  if (prereqs.length === 0) return 0;

  const maxPrereqDepth = Math.max(...prereqs.map(pId => calculateQuestDepth(pId, visited)));
  return maxPrereqDepth + 1;
}

const questProgression = {};
rawQuests.forEach(q => {
  const depth = calculateQuestDepth(q.id);
  const level = q.require?.level || 1;
  const normalizedTitle = q.title.toUpperCase().replace(/[^A-Z0-9]/g, '_');

  questProgression[normalizedTitle] = {
    id: q.id,
    title: q.title,
    level: level,
    depth: depth,
    priority: level * 10 + depth
  };
});

// ============================================
// Process FiR Items
// ============================================

const itemSummary = {};

for (const [itemId, itemData] of Object.entries(firItems)) {
  const questRequirements = itemData.quest || {};
  const totalQuestCount = Object.values(questRequirements).reduce((sum, count) => sum + count, 0);

  if (totalQuestCount > 0) {
    let earliestQuest = null;
    let earliestPriority = Infinity;

    const questBreakdown = Object.entries(questRequirements).map(([questId, count]) => {
      const progression = questProgression[questId];
      const questInfo = {
        questId,
        questName: firQuests[questId]?.name?.en || questId,
        count,
        dealer: firQuests[questId]?.dealer || 'Unknown',
        kappa: firQuests[questId]?.kappa || false,
        level: progression?.level || 1,
        depth: progression?.depth || 0,
        priority: progression?.priority || 999
      };

      if (questInfo.priority < earliestPriority) {
        earliestPriority = questInfo.priority;
        earliestQuest = questInfo;
      }

      return questInfo;
    });

    questBreakdown.sort((a, b) => a.priority - b.priority);

    itemSummary[itemId] = {
      name: itemData.name?.en || itemId,
      nameShort: itemData.nameShort?.en || itemData.name?.en || itemId,
      type: itemData.type || 'Unknown',
      totalRequired: totalQuestCount,
      questBreakdown,
      earliestAccess: earliestQuest ? {
        questName: earliestQuest.questName,
        level: earliestQuest.level,
        depth: earliestQuest.depth,
        priority: earliestQuest.priority
      } : null,
      canCraft: !!itemData.craft,
      craftLocations: itemData.craft ? Object.keys(itemData.craft) : []
    };
  }
}

// Sort by priority (earlier access first)
const sortedItems = Object.entries(itemSummary)
  .sort((a, b) => {
    const priorityA = a[1].earliestAccess?.priority || 999;
    const priorityB = b[1].earliestAccess?.priority || 999;
    if (priorityA !== priorityB) return priorityA - priorityB;
    return b[1].totalRequired - a[1].totalRequired;
  });

// ============================================
// Create Final Data Structure
// ============================================

const processedData = {
  metadata: {
    generatedAt: new Date().toISOString(),
    source: 'fakundo/tarkov-raid-items + TarkovTracker/tarkovdata',
    totalUniqueItems: sortedItems.length,
    totalItemsNeeded: sortedItems.reduce((sum, [, item]) => sum + item.totalRequired, 0)
  },
  items: Object.fromEntries(sortedItems),
  quests: firQuests,
  questProgression
};

// Write processed data
fs.mkdirSync(PROCESSED_DIR, { recursive: true });
fs.writeFileSync(
  path.join(PROCESSED_DIR, 'fir-requirements.json'),
  JSON.stringify(processedData, null, 2)
);

// Create summary
const progressionSummary = sortedItems.map(([id, item]) => ({
  id,
  name: item.name,
  total: item.totalRequired,
  type: item.type,
  level: item.earliestAccess?.level || '?',
  priority: item.earliestAccess?.priority || 999,
  firstQuest: item.earliestAccess?.questName || 'Unknown',
  canCraft: item.canCraft
}));

fs.writeFileSync(
  path.join(PROCESSED_DIR, 'fir-summary.json'),
  JSON.stringify(progressionSummary, null, 2)
);

// ============================================
// Output Summary
// ============================================

console.log('=== Tarkov FiR Data Processing Complete ===');
console.log(`FiR Items: ${processedData.metadata.totalUniqueItems}`);
console.log(`Total needed: ${processedData.metadata.totalItemsNeeded}`);

console.log('\n=== Early Game (Lv1-10) ===');
sortedItems
  .filter(([, item]) => (item.earliestAccess?.level || 99) <= 10)
  .slice(0, 10)
  .forEach(([id, item]) => {
    const craft = item.canCraft ? ' [Craft可]' : '';
    console.log(`  Lv${item.earliestAccess.level} ${item.name}: ${item.totalRequired}x${craft}`);
  });

console.log('\n=== Mid Game (Lv11-25) ===');
sortedItems
  .filter(([, item]) => {
    const lvl = item.earliestAccess?.level || 99;
    return lvl >= 11 && lvl <= 25;
  })
  .slice(0, 10)
  .forEach(([id, item]) => {
    const craft = item.canCraft ? ' [Craft可]' : '';
    console.log(`  Lv${item.earliestAccess.level} ${item.name}: ${item.totalRequired}x${craft}`);
  });
