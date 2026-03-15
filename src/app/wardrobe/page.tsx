'use client';

import { useState, useEffect } from 'react';
import Link from 'next/link';
import {
  Upload,
  Sparkles,
  Star,
  Filter,
  TrendingUp,
  Palette,
  Calendar,
} from 'lucide-react';
import { getAllOutfits } from '@/lib/storage';
import { computeStyleDNA } from '@/lib/styleDNA';
import { formatDateShort, daysAgo } from '@/lib/exif';
import type { OutfitMeta, Occasion, Season } from '@/lib/types';

const OCCASION_LABELS: Record<Occasion, string> = {
  casual: 'Casual',
  work: 'Work',
  formal: 'Formal',
  sport: 'Sport',
  evening: 'Evening',
  weekend: 'Weekend',
  travel: 'Travel',
};

const SEASON_LABELS: Record<Season, string> = {
  spring: '🌸 Spring',
  summer: '☀️ Summer',
  fall: '🍂 Fall',
  winter: '❄️ Winter',
  'all-season': '🌿 All Season',
};

type Filter = 'all' | Occasion | Season;

function OutfitCard({ outfit }: { outfit: OutfitMeta }) {
  const days = daysAgo(outfit.wornDate);
  return (
    <Link href={`/outfit/${outfit.id}`} className="group">
      <div className="aspect-[3/4] rounded-2xl overflow-hidden bg-sand-100 relative mb-3">
        {outfit.thumbnailDataUrl ? (
          // eslint-disable-next-line @next/next/no-img-element
          <img
            src={outfit.thumbnailDataUrl}
            alt={outfit.analysis.title}
            className="w-full h-full object-cover group-hover:scale-105 transition-transform duration-300"
          />
        ) : (
          <div className="w-full h-full flex items-center justify-center">
            <Sparkles className="w-8 h-8 text-sand-300" />
          </div>
        )}

        {/* Versatility score */}
        <div className="absolute top-2 right-2 bg-white/90 backdrop-blur-sm rounded-full px-2 py-0.5 flex items-center gap-1 text-xs font-semibold text-ink shadow-sm">
          <Star size={10} className="text-camel-400 fill-camel-400" />
          {outfit.analysis.versatilityScore}
        </div>

        {/* Style chip */}
        <div className="absolute bottom-2 left-2 bg-forest-600/90 text-white text-[10px] font-semibold px-2 py-0.5 rounded-full backdrop-blur-sm">
          {outfit.analysis.style}
        </div>
      </div>

      <div>
        <p className="font-semibold text-ink text-sm leading-tight line-clamp-1">
          {outfit.analysis.title}
        </p>
        <p className="text-xs text-[#6B6B6E] mt-0.5">
          {days === 0 ? 'Today' : days === 1 ? 'Yesterday' : `${days}d ago`}
          {' · '}
          {formatDateShort(outfit.wornDate)}
        </p>

        {/* Color dots */}
        <div className="flex gap-1 mt-2">
          {outfit.analysis.colors.slice(0, 4).map((c, i) => (
            <div
              key={i}
              className="w-3 h-3 rounded-full border border-white shadow-sm ring-1 ring-sand-200"
              style={{ backgroundColor: c.hex }}
              title={c.name}
            />
          ))}
        </div>
      </div>
    </Link>
  );
}

export default function WardrobePage() {
  const [outfits, setOutfits] = useState<OutfitMeta[]>([]);
  const [activeFilter, setActiveFilter] = useState<Filter>('all');
  const [mounted, setMounted] = useState(false);

  useEffect(() => {
    setOutfits(getAllOutfits());
    setMounted(true);
    const handler = () => setOutfits(getAllOutfits());
    window.addEventListener('wardrobe-updated', handler);
    return () => window.removeEventListener('wardrobe-updated', handler);
  }, []);

  const dna = computeStyleDNA(outfits);

  const filteredOutfits = outfits.filter((o) => {
    if (activeFilter === 'all') return true;
    return (
      o.analysis.occasions.includes(activeFilter as Occasion) ||
      o.analysis.seasons.includes(activeFilter as Season)
    );
  });

  const allFilters: { key: Filter; label: string }[] = [
    { key: 'all', label: 'All' },
    ...Object.entries(OCCASION_LABELS).map(([k, v]) => ({ key: k as Filter, label: v })),
    ...Object.entries(SEASON_LABELS).map(([k, v]) => ({ key: k as Filter, label: v })),
  ];

  if (!mounted) return null;

  // ─── Empty state ───────────────────────────────────────────────────────────
  if (outfits.length === 0) {
    return (
      <div className="max-w-2xl mx-auto px-4 py-16 flex flex-col items-center text-center animate-fade-in">
        <div className="w-20 h-20 bg-sand-100 rounded-3xl flex items-center justify-center mb-6">
          <Sparkles className="w-9 h-9 text-[#6B6B6E]" />
        </div>
        <h1 className="text-2xl font-bold text-ink mb-3">Your Wardrobe is Empty</h1>
        <p className="text-[#6B6B6E] leading-relaxed mb-8 max-w-sm">
          Upload your first outfit to start building your digital wardrobe and unlock Style DNA insights.
        </p>
        <Link
          href="/upload"
          className="bg-forest-600 text-white px-8 py-4 rounded-2xl font-semibold flex items-center gap-2 hover:bg-forest-700 transition-colors"
        >
          <Upload size={18} />
          Upload an outfit
        </Link>
      </div>
    );
  }

  return (
    <div className="max-w-2xl mx-auto px-4 py-8 animate-fade-in">
      <div className="flex items-center justify-between mb-6">
        <div>
          <h1 className="text-2xl font-bold text-ink">My Wardrobe</h1>
          <p className="text-sm text-[#6B6B6E] mt-1">{outfits.length} outfits</p>
        </div>
        <Link
          href="/upload"
          className="flex items-center gap-2 bg-forest-600 text-white px-4 py-2 rounded-xl text-sm font-semibold hover:bg-forest-700 transition-colors"
        >
          <Upload size={15} />
          Add
        </Link>
      </div>

      {/* ─── Style DNA Card ─────────────────────────────────────────────────── */}
      {outfits.length >= 2 && (
        <div className="bg-ink rounded-2xl p-5 mb-8 text-white">
          <div className="flex items-start justify-between mb-4">
            <div>
              <div className="flex items-center gap-2 mb-1">
                <Sparkles size={14} className="text-camel-400" />
                <span className="text-xs font-semibold text-white/60 uppercase tracking-wider">
                  Style DNA
                </span>
              </div>
              <h2 className="text-xl font-bold">{dna.dominantStyle}</h2>
            </div>
            <div className="flex items-center gap-1 bg-white/10 rounded-full px-3 py-1">
              <Star size={12} className="text-camel-400 fill-camel-400" />
              <span className="text-sm font-semibold">{dna.averageVersatility}</span>
            </div>
          </div>

          {/* Color palette row */}
          {dna.topColors.length > 0 && (
            <div className="mb-4">
              <p className="text-xs text-white/50 mb-2 flex items-center gap-1">
                <Palette size={11} /> Top Colors
              </p>
              <div className="flex gap-3">
                {dna.topColors.map((c, i) => (
                  <div key={i} className="flex flex-col items-center gap-1">
                    <div
                      className="w-8 h-8 rounded-full border-2 border-white/20 shadow"
                      style={{ backgroundColor: c.hex }}
                    />
                    <span className="text-[9px] text-white/50 text-center leading-tight max-w-[32px] truncate">
                      {c.name}
                    </span>
                  </div>
                ))}
              </div>
            </div>
          )}

          <div className="grid grid-cols-3 gap-3 mt-4 pt-4 border-t border-white/10">
            <div>
              <p className="text-2xl font-bold">{dna.totalOutfits}</p>
              <p className="text-xs text-white/50 mt-0.5">Outfits</p>
            </div>
            <div>
              <p className="text-2xl font-bold">{dna.uniqueColors}</p>
              <p className="text-xs text-white/50 mt-0.5">Colors</p>
            </div>
            <div>
              {dna.topOccasions[0] && (
                <>
                  <p className="text-sm font-bold capitalize mt-1">{dna.topOccasions[0].occasion}</p>
                  <p className="text-xs text-white/50 mt-0.5">Top occasion</p>
                </>
              )}
            </div>
          </div>

          {/* Combination teaser */}
          {outfits.length >= 4 && (
            <div className="mt-4 pt-4 border-t border-white/10 flex items-center gap-2">
              <TrendingUp size={14} className="text-camel-400 flex-shrink-0" />
              <p className="text-xs text-white/70">
                You have {outfits.length} outfits — Claude can suggest new combinations!{' '}
                <span className="text-camel-400 font-medium">Coming soon</span>
              </p>
            </div>
          )}
        </div>
      )}

      {/* ─── Filters ─────────────────────────────────────────────────────────── */}
      <div className="flex gap-2 overflow-x-auto pb-2 mb-6 scrollbar-hide">
        <div className="flex items-center gap-1.5 text-xs text-[#6B6B6E] flex-shrink-0">
          <Filter size={12} />
        </div>
        {allFilters.map(({ key, label }) => (
          <button
            key={key}
            onClick={() => setActiveFilter(key)}
            className={`flex-shrink-0 text-xs font-medium px-3 py-1.5 rounded-full transition-colors ${
              activeFilter === key
                ? 'bg-forest-600 text-white'
                : 'bg-sand-100 text-[#6B6B6E] hover:bg-sand-200'
            }`}
          >
            {label}
          </button>
        ))}
      </div>

      {/* ─── Outfit grid ──────────────────────────────────────────────────────── */}
      {filteredOutfits.length === 0 ? (
        <div className="text-center py-16">
          <p className="text-[#6B6B6E] text-sm">
            No outfits match this filter yet.
          </p>
        </div>
      ) : (
        <div className="grid grid-cols-2 sm:grid-cols-3 gap-4">
          {filteredOutfits.map((o) => (
            <OutfitCard key={o.id} outfit={o} />
          ))}
        </div>
      )}

      {/* Calendar link */}
      <div className="mt-10 bg-sand-50 border border-sand-200 rounded-xl p-4 flex items-center gap-3">
        <Calendar size={18} className="text-forest-600 flex-shrink-0" />
        <div className="flex-1">
          <p className="text-sm font-semibold text-ink">See your outfit history</p>
          <p className="text-xs text-[#6B6B6E] mt-0.5">View what you wore on each day</p>
        </div>
        <Link
          href="/calendar"
          className="text-xs font-semibold text-forest-600 hover:underline flex-shrink-0"
        >
          Calendar →
        </Link>
      </div>
    </div>
  );
}
