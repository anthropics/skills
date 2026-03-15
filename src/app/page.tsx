'use client';

import { useState, useEffect } from 'react';
import Link from 'next/link';
import { Upload, Sparkles, Calendar, Star, TrendingUp, Clock } from 'lucide-react';
import { getAllOutfits } from '@/lib/storage';
import { formatDateShort, daysAgo, todayISO } from '@/lib/exif';
import { computeStyleDNA } from '@/lib/styleDNA';
import type { OutfitMeta } from '@/lib/types';

function OutfitThumb({ outfit }: { outfit: OutfitMeta }) {
  return (
    <Link href={`/outfit/${outfit.id}`} className="group">
      <div className="aspect-[3/4] rounded-xl overflow-hidden bg-sand-100 relative">
        {outfit.thumbnailDataUrl ? (
          // eslint-disable-next-line @next/next/no-img-element
          <img
            src={outfit.thumbnailDataUrl}
            alt={outfit.analysis.title}
            className="w-full h-full object-cover group-hover:scale-105 transition-transform duration-300"
          />
        ) : (
          <div className="w-full h-full flex items-center justify-center">
            <Sparkles className="w-6 h-6 text-sand-400" />
          </div>
        )}
      </div>
      <p className="text-xs font-medium text-ink mt-2 line-clamp-1">{outfit.analysis.title}</p>
      <p className="text-xs text-[#6B6B6E]">{formatDateShort(outfit.wornDate)}</p>
    </Link>
  );
}

export default function HomePage() {
  const [outfits, setOutfits] = useState<OutfitMeta[]>([]);
  const [mounted, setMounted] = useState(false);

  useEffect(() => {
    setOutfits(getAllOutfits());
    setMounted(true);

    const handler = () => setOutfits(getAllOutfits());
    window.addEventListener('wardrobe-updated', handler);
    return () => window.removeEventListener('wardrobe-updated', handler);
  }, []);

  if (!mounted) return null;

  const dna = computeStyleDNA(outfits);
  const today = todayISO();
  const todayOutfits = outfits.filter((o) => o.wornDate === today);
  const recentOutfits = outfits.slice(0, 6);
  const daysSinceUpload = dna.lastUploadedAt
    ? daysAgo(dna.lastUploadedAt.split('T')[0])
    : null;

  // ─── Empty state ──────────────────────────────────────────────────────────
  if (outfits.length === 0) {
    return (
      <div className="max-w-xl mx-auto px-4 py-16 flex flex-col items-center text-center animate-fade-in">
        <div className="w-20 h-20 bg-sand-100 rounded-3xl flex items-center justify-center mb-6">
          <Sparkles className="w-9 h-9 text-[#6B6B6E]" />
        </div>
        <h1 className="text-2xl font-bold text-ink mb-3">Welcome to Wardrobe AI</h1>
        <p className="text-[#6B6B6E] leading-relaxed mb-8 max-w-sm">
          Upload your first outfit photo to get AI-powered style analysis, a color palette,
          tips, and start tracking what you wear.
        </p>

        <Link
          href="/upload"
          className="w-full max-w-xs bg-forest-600 text-white py-4 rounded-2xl font-semibold flex items-center justify-center gap-2 hover:bg-forest-700 transition-colors"
        >
          <Upload size={18} />
          Upload your first outfit
        </Link>

        <div className="mt-12 grid grid-cols-3 gap-4 text-center w-full max-w-sm">
          {[
            { icon: '🎨', label: 'Color Analysis' },
            { icon: '💡', label: 'Style Tips' },
            { icon: '📅', label: 'Outfit Calendar' },
          ].map(({ icon, label }) => (
            <div key={label} className="bg-white rounded-xl p-4 border border-sand-200">
              <span className="text-2xl block mb-2">{icon}</span>
              <p className="text-xs font-medium text-[#6B6B6E]">{label}</p>
            </div>
          ))}
        </div>
      </div>
    );
  }

  // ─── Dashboard ────────────────────────────────────────────────────────────
  return (
    <div className="max-w-2xl mx-auto px-4 py-8 animate-fade-in">
      {/* Morning greeting */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-ink">Good morning ✨</h1>
        <p className="text-[#6B6B6E] mt-1">
          {todayOutfits.length > 0
            ? `You've logged today's outfit.`
            : `What are you wearing today?`}
        </p>
      </div>

      {/* Today's outfit or CTA */}
      {todayOutfits.length > 0 ? (
        <section className="mb-8">
          <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider mb-3 flex items-center gap-2">
            <Calendar size={14} />
            Today
          </h2>
          <div className="grid grid-cols-2 sm:grid-cols-3 gap-4">
            {todayOutfits.map((o) => <OutfitThumb key={o.id} outfit={o} />)}
            <Link
              href="/upload"
              className="aspect-[3/4] rounded-xl border-2 border-dashed border-sand-300 flex flex-col items-center justify-center gap-2 hover:border-forest-600 hover:bg-sand-50 transition-all group"
            >
              <Upload size={20} className="text-[#6B6B6E] group-hover:text-forest-600 transition-colors" />
              <span className="text-xs font-medium text-[#6B6B6E] group-hover:text-forest-600 transition-colors">Add outfit</span>
            </Link>
          </div>
        </section>
      ) : (
        <Link
          href="/upload"
          className="block mb-8 bg-gradient-to-r from-forest-600 to-forest-700 text-white rounded-2xl p-6 hover:opacity-95 transition-opacity"
        >
          <div className="flex items-center justify-between">
            <div>
              <p className="font-semibold text-lg">Log today&apos;s outfit</p>
              <p className="text-white/70 text-sm mt-1">Upload a photo for instant style analysis</p>
            </div>
            <div className="w-12 h-12 bg-white/20 rounded-xl flex items-center justify-center">
              <Upload size={22} className="text-white" />
            </div>
          </div>
        </Link>
      )}

      {/* Stats strip */}
      <div className="grid grid-cols-3 gap-3 mb-8">
        <div className="bg-white rounded-xl p-4 border border-sand-200 text-center shadow-sm">
          <p className="text-2xl font-bold text-ink">{dna.totalOutfits}</p>
          <p className="text-xs text-[#6B6B6E] mt-1">Outfits</p>
        </div>
        <div className="bg-white rounded-xl p-4 border border-sand-200 text-center shadow-sm">
          <p className="text-2xl font-bold text-ink">{dna.uniqueColors}</p>
          <p className="text-xs text-[#6B6B6E] mt-1">Colors</p>
        </div>
        <div className="bg-white rounded-xl p-4 border border-sand-200 text-center shadow-sm">
          <p className="text-2xl font-bold text-ink">{dna.averageVersatility}</p>
          <p className="text-xs text-[#6B6B6E] mt-1 flex items-center justify-center gap-1">
            <Star size={10} className="text-camel-400 fill-camel-400" />
            Versatility
          </p>
        </div>
      </div>

      {/* Nudge: hasn't uploaded in a while */}
      {daysSinceUpload !== null && daysSinceUpload >= 3 && (
        <div className="bg-camel-400/10 border border-camel-400/30 rounded-xl p-4 mb-8 flex gap-3">
          <Clock size={18} className="text-camel-500 flex-shrink-0 mt-0.5" />
          <div>
            <p className="text-sm font-semibold text-ink">
              {daysSinceUpload === 3 ? `Last upload was 3 days ago` : `You haven't uploaded in ${daysSinceUpload} days`}
            </p>
            <p className="text-xs text-[#6B6B6E] mt-1">
              Keep your wardrobe journal going!{' '}
              <Link href="/upload" className="text-forest-600 font-medium hover:underline">
                Add an outfit
              </Link>
            </p>
          </div>
        </div>
      )}

      {/* Rewear suggestion: outfit worn longest ago */}
      {dna.oldestUnworn && daysAgo(dna.oldestUnworn.wornDate) >= 14 && (
        <div className="bg-sand-50 border border-sand-200 rounded-xl p-4 mb-8 flex gap-3">
          <TrendingUp size={18} className="text-forest-600 flex-shrink-0 mt-0.5" />
          <div className="flex-1 min-w-0">
            <p className="text-sm font-semibold text-ink">Rewear idea</p>
            <p className="text-xs text-[#6B6B6E] mt-0.5 truncate">
              &ldquo;{dna.oldestUnworn.analysis.title}&rdquo; — worn {daysAgo(dna.oldestUnworn.wornDate)} days ago
            </p>
          </div>
          <Link
            href={`/outfit/${dna.oldestUnworn.id}`}
            className="flex-shrink-0 text-xs font-medium text-forest-600 hover:underline self-center"
          >
            View
          </Link>
        </div>
      )}

      {/* Style DNA teaser */}
      {outfits.length >= 3 && (
        <section className="mb-8">
          <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider mb-3 flex items-center gap-2">
            <Sparkles size={14} />
            Your Style DNA
          </h2>
          <div className="bg-white rounded-xl p-4 border border-sand-200 shadow-sm">
            <p className="font-semibold text-ink mb-3">{dna.dominantStyle}</p>
            <div className="flex gap-2 flex-wrap">
              {dna.topColors.slice(0, 5).map((c, i) => (
                <div
                  key={i}
                  className="w-8 h-8 rounded-full border-2 border-white shadow-sm ring-1 ring-sand-200"
                  style={{ backgroundColor: c.hex }}
                  title={c.name}
                />
              ))}
            </div>
            <Link
              href="/wardrobe"
              className="mt-3 text-xs font-medium text-forest-600 hover:underline block"
            >
              See full wardrobe analysis →
            </Link>
          </div>
        </section>
      )}

      {/* Recent outfits */}
      <section>
        <div className="flex items-center justify-between mb-3">
          <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider">
            Recent Outfits
          </h2>
          <Link href="/wardrobe" className="text-xs font-medium text-forest-600 hover:underline">
            View all
          </Link>
        </div>
        <div className="grid grid-cols-3 sm:grid-cols-4 gap-3">
          {recentOutfits.map((o) => <OutfitThumb key={o.id} outfit={o} />)}
        </div>
      </section>
    </div>
  );
}
