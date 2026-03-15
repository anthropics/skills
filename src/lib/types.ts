// ─── Core domain types ────────────────────────────────────────────────────────

export interface ClothingItem {
  category: 'top' | 'bottom' | 'dress' | 'outerwear' | 'shoes' | 'bag' | 'accessory' | 'other';
  name: string;
  fabric?: string;
  color?: string;
}

export interface ColorSwatch {
  name: string;
  hex: string;
  percentage: number;
}

export type Occasion = 'casual' | 'work' | 'formal' | 'sport' | 'evening' | 'weekend' | 'travel';
export type Season = 'spring' | 'summer' | 'fall' | 'winter' | 'all-season';

export interface OutfitAnalysis {
  title: string;
  description: string;
  style: string;           // e.g. "Casual Chic", "Minimalist"
  mood: string;            // e.g. "Confident", "Relaxed"
  occasions: Occasion[];
  seasons: Season[];
  colors: ColorSwatch[];
  items: ClothingItem[];
  tips: string[];
  versatilityScore: number;  // 1–10
  confidence?: string;       // e.g. "perfect for a first date" — one-liner booster
}

export interface Outfit {
  id: string;
  wornDate: string;          // ISO date string (YYYY-MM-DD)
  uploadedAt: string;        // ISO datetime
  analysis: OutfitAnalysis;
  imageKey: string;          // IndexedDB key for the processed image blob
  thumbnailDataUrl?: string; // small base64 for quick renders
  source: 'exif' | 'manual'; // whether date came from photo metadata
  notes?: string;
}

// ─── Storage types ─────────────────────────────────────────────────────────────

export interface OutfitMeta {
  id: string;
  wornDate: string;
  uploadedAt: string;
  analysis: OutfitAnalysis;
  imageKey: string;
  thumbnailDataUrl?: string;
  source: 'exif' | 'manual';
  notes?: string;
}

// ─── Derived / view types ──────────────────────────────────────────────────────

export interface StyleDNA {
  topColors: ColorSwatch[];
  topOccasions: { occasion: Occasion; count: number }[];
  topSeasons: { season: Season; count: number }[];
  dominantStyle: string;
  totalOutfits: number;
  uniqueColors: number;
  averageVersatility: number;
  lastUploadedAt: string | null;
  oldestUnworn: Outfit | null;  // outfit not worn in longest time
}

export interface CalendarDay {
  date: string;   // YYYY-MM-DD
  outfits: Outfit[];
}

export interface CombinationSuggestion {
  title: string;
  items: string[];   // outfit IDs
  description: string;
  occasion: Occasion;
}
