'use client';

import { openDB, IDBPDatabase } from 'idb';
import type { Outfit, OutfitMeta } from './types';

const DB_NAME = 'wardrobe-ai';
const DB_VERSION = 1;
const IMAGES_STORE = 'images';
const META_KEY = 'wardrobe-meta';

let dbPromise: Promise<IDBPDatabase> | null = null;

function getDB(): Promise<IDBPDatabase> {
  if (!dbPromise) {
    dbPromise = openDB(DB_NAME, DB_VERSION, {
      upgrade(db) {
        if (!db.objectStoreNames.contains(IMAGES_STORE)) {
          db.createObjectStore(IMAGES_STORE);
        }
      },
    });
  }
  return dbPromise;
}

// ─── Image storage (IndexedDB) ─────────────────────────────────────────────────

export async function saveImage(key: string, blob: Blob): Promise<void> {
  const db = await getDB();
  await db.put(IMAGES_STORE, blob, key);
}

export async function loadImage(key: string): Promise<Blob | undefined> {
  const db = await getDB();
  return db.get(IMAGES_STORE, key);
}

export async function deleteImage(key: string): Promise<void> {
  const db = await getDB();
  await db.delete(IMAGES_STORE, key);
}

export async function loadImageAsUrl(key: string): Promise<string | null> {
  const blob = await loadImage(key);
  if (!blob) return null;
  return URL.createObjectURL(blob);
}

// ─── Outfit metadata (localStorage) ───────────────────────────────────────────

function loadMeta(): OutfitMeta[] {
  if (typeof window === 'undefined') return [];
  try {
    const raw = localStorage.getItem(META_KEY);
    return raw ? JSON.parse(raw) : [];
  } catch {
    return [];
  }
}

function saveMeta(outfits: OutfitMeta[]): void {
  localStorage.setItem(META_KEY, JSON.stringify(outfits));
}

export function getAllOutfits(): OutfitMeta[] {
  return loadMeta().sort(
    (a, b) => new Date(b.wornDate).getTime() - new Date(a.wornDate).getTime()
  );
}

export function getOutfitById(id: string): OutfitMeta | undefined {
  return loadMeta().find((o) => o.id === id);
}

export function saveOutfit(outfit: OutfitMeta): void {
  const outfits = loadMeta();
  const idx = outfits.findIndex((o) => o.id === outfit.id);
  if (idx >= 0) {
    outfits[idx] = outfit;
  } else {
    outfits.push(outfit);
  }
  saveMeta(outfits);
}

export function deleteOutfit(id: string): void {
  const outfits = loadMeta().filter((o) => o.id !== id);
  saveMeta(outfits);
}

export function getOutfitsByDate(date: string): OutfitMeta[] {
  return loadMeta().filter((o) => o.wornDate === date);
}

export function getOutfitsByMonth(year: number, month: number): OutfitMeta[] {
  const prefix = `${year}-${String(month).padStart(2, '0')}`;
  return loadMeta().filter((o) => o.wornDate.startsWith(prefix));
}

// ─── Helpers ───────────────────────────────────────────────────────────────────

export function generateId(): string {
  return `outfit-${Date.now()}-${Math.random().toString(36).slice(2, 9)}`;
}

/** Resize an image blob to a tiny thumbnail (for calendar renders). */
export async function createThumbnail(
  imageBlob: Blob,
  size = 120
): Promise<string> {
  return new Promise((resolve) => {
    const url = URL.createObjectURL(imageBlob);
    const img = new Image();
    img.onload = () => {
      const canvas = document.createElement('canvas');
      const ratio = Math.min(size / img.width, size / img.height);
      canvas.width = img.width * ratio;
      canvas.height = img.height * ratio;
      const ctx = canvas.getContext('2d')!;
      ctx.drawImage(img, 0, 0, canvas.width, canvas.height);
      URL.revokeObjectURL(url);
      resolve(canvas.toDataURL('image/jpeg', 0.7));
    };
    img.src = url;
  });
}
