import type { OutfitMeta, StyleDNA, ColorSwatch, Occasion, Season } from './types';
import { daysAgo } from './exif';

export function computeStyleDNA(outfits: OutfitMeta[]): StyleDNA {
  if (outfits.length === 0) {
    return {
      topColors: [],
      topOccasions: [],
      topSeasons: [],
      dominantStyle: 'Not enough data yet',
      totalOutfits: 0,
      uniqueColors: 0,
      averageVersatility: 0,
      lastUploadedAt: null,
      oldestUnworn: null,
    };
  }

  // ─── Colors ────────────────────────────────────────────────────────────────
  const colorMap = new Map<string, { swatch: ColorSwatch; total: number; count: number }>();
  for (const outfit of outfits) {
    for (const color of outfit.analysis.colors) {
      const key = color.name.toLowerCase();
      const existing = colorMap.get(key);
      if (existing) {
        existing.total += color.percentage;
        existing.count += 1;
      } else {
        colorMap.set(key, { swatch: color, total: color.percentage, count: 1 });
      }
    }
  }
  const topColors: ColorSwatch[] = [...colorMap.values()]
    .sort((a, b) => b.total / b.count - a.total / a.count)
    .slice(0, 6)
    .map(({ swatch, total, count }) => ({
      ...swatch,
      percentage: Math.round(total / count),
    }));
  const uniqueColors = colorMap.size;

  // ─── Occasions ─────────────────────────────────────────────────────────────
  const occasionMap = new Map<Occasion, number>();
  for (const outfit of outfits) {
    for (const occ of outfit.analysis.occasions) {
      occasionMap.set(occ, (occasionMap.get(occ) ?? 0) + 1);
    }
  }
  const topOccasions = [...occasionMap.entries()]
    .sort((a, b) => b[1] - a[1])
    .slice(0, 3)
    .map(([occasion, count]) => ({ occasion, count }));

  // ─── Seasons ───────────────────────────────────────────────────────────────
  const seasonMap = new Map<Season, number>();
  for (const outfit of outfits) {
    for (const s of outfit.analysis.seasons) {
      seasonMap.set(s, (seasonMap.get(s) ?? 0) + 1);
    }
  }
  const topSeasons = [...seasonMap.entries()]
    .sort((a, b) => b[1] - a[1])
    .slice(0, 3)
    .map(([season, count]) => ({ season, count }));

  // ─── Dominant style ────────────────────────────────────────────────────────
  const styleMap = new Map<string, number>();
  for (const outfit of outfits) {
    styleMap.set(outfit.analysis.style, (styleMap.get(outfit.analysis.style) ?? 0) + 1);
  }
  const dominantStyle = [...styleMap.entries()].sort((a, b) => b[1] - a[1])[0]?.[0] ?? 'Mixed';

  // ─── Versatility ──────────────────────────────────────────────────────────
  const averageVersatility =
    Math.round(
      (outfits.reduce((sum, o) => sum + o.analysis.versatilityScore, 0) / outfits.length) * 10
    ) / 10;

  // ─── Last uploaded ─────────────────────────────────────────────────────────
  const lastUploadedAt = outfits
    .map((o) => o.uploadedAt)
    .sort()
    .reverse()[0] ?? null;

  // ─── Oldest unworn (longest since worn) ───────────────────────────────────
  const oldestUnworn = outfits.length > 0
    ? outfits.reduce((oldest, current) =>
        daysAgo(current.wornDate) > daysAgo(oldest.wornDate) ? current : oldest
      )
    : null;

  return {
    topColors,
    topOccasions,
    topSeasons,
    dominantStyle,
    totalOutfits: outfits.length,
    uniqueColors,
    averageVersatility,
    lastUploadedAt,
    oldestUnworn,
  };
}
