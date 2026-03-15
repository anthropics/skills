'use client';

import { useState, useEffect, useCallback } from 'react';
import { getAllOutfits, saveOutfit, deleteOutfit, deleteImage } from '@/lib/storage';
import type { OutfitMeta } from '@/lib/types';

export function useOutfits() {
  const [outfits, setOutfits] = useState<OutfitMeta[]>([]);
  const [loading, setLoading] = useState(true);

  const refresh = useCallback(() => {
    setOutfits(getAllOutfits());
    setLoading(false);
  }, []);

  useEffect(() => {
    refresh();

    // Listen for storage events (cross-tab sync)
    const handleStorage = () => refresh();
    window.addEventListener('storage', handleStorage);
    window.addEventListener('wardrobe-updated', handleStorage);
    return () => {
      window.removeEventListener('storage', handleStorage);
      window.removeEventListener('wardrobe-updated', handleStorage);
    };
  }, [refresh]);

  const addOutfit = useCallback((outfit: OutfitMeta) => {
    saveOutfit(outfit);
    setOutfits(getAllOutfits());
    window.dispatchEvent(new Event('wardrobe-updated'));
  }, []);

  const removeOutfit = useCallback(async (id: string, imageKey: string) => {
    deleteOutfit(id);
    await deleteImage(imageKey);
    setOutfits(getAllOutfits());
    window.dispatchEvent(new Event('wardrobe-updated'));
  }, []);

  return { outfits, loading, refresh, addOutfit, removeOutfit };
}
