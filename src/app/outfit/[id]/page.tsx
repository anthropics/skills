'use client';

import { useState, useEffect } from 'react';
import { useParams, useRouter } from 'next/navigation';
import Link from 'next/link';
import {
  ArrowLeft,
  Trash2,
  Sparkles,
  Star,
  Palette,
  Tag,
  Lightbulb,
  Calendar,
  Shirt,
} from 'lucide-react';
import { getOutfitById } from '@/lib/storage';
import { loadImageAsUrl, deleteOutfit, deleteImage } from '@/lib/storage';
import { formatDate } from '@/lib/exif';
import type { OutfitMeta, ClothingItem } from '@/lib/types';

const CATEGORY_EMOJI: Record<ClothingItem['category'], string> = {
  top: '👕',
  bottom: '👖',
  dress: '👗',
  outerwear: '🧥',
  shoes: '👟',
  bag: '👜',
  accessory: '💍',
  other: '🎽',
};

const OCCASION_LABEL: Record<string, string> = {
  casual: 'Casual',
  work: 'Work',
  formal: 'Formal',
  sport: 'Sport',
  evening: 'Evening',
  weekend: 'Weekend',
  travel: 'Travel',
};

const SEASON_LABEL: Record<string, string> = {
  spring: '🌸 Spring',
  summer: '☀️ Summer',
  fall: '🍂 Fall',
  winter: '❄️ Winter',
  'all-season': '🌿 All Season',
};

export default function OutfitDetailPage() {
  const { id } = useParams();
  const router = useRouter();

  const [outfit, setOutfit] = useState<OutfitMeta | null>(null);
  const [imageUrl, setImageUrl] = useState<string | null>(null);
  const [loading, setLoading] = useState(true);
  const [deleting, setDeleting] = useState(false);

  useEffect(() => {
    const meta = getOutfitById(id as string);
    if (!meta) {
      router.replace('/wardrobe');
      return;
    }
    setOutfit(meta);
    loadImageAsUrl(meta.imageKey).then((url) => {
      setImageUrl(url);
      setLoading(false);
    });
  }, [id, router]);

  const handleDelete = async () => {
    if (!outfit || deleting) return;
    if (!confirm('Remove this outfit from your wardrobe?')) return;
    setDeleting(true);
    deleteOutfit(outfit.id);
    await deleteImage(outfit.imageKey);
    router.push('/wardrobe');
  };

  if (loading || !outfit) {
    return (
      <div className="max-w-2xl mx-auto px-4 py-12">
        <div className="h-64 rounded-2xl shimmer mb-6" />
        <div className="h-8 w-48 rounded-lg shimmer mb-4" />
        <div className="h-4 w-full rounded shimmer mb-2" />
        <div className="h-4 w-3/4 rounded shimmer" />
      </div>
    );
  }

  const { analysis } = outfit;

  return (
    <div className="max-w-2xl mx-auto px-4 py-8 animate-slide-up">
      {/* Back */}
      <Link
        href="/wardrobe"
        className="inline-flex items-center gap-2 text-sm text-[#6B6B6E] hover:text-ink mb-6 transition-colors"
      >
        <ArrowLeft size={16} />
        Wardrobe
      </Link>

      {/* Hero */}
      <div className="rounded-2xl overflow-hidden bg-sand-100 aspect-[3/4] md:aspect-video relative mb-6">
        {imageUrl ? (
          // eslint-disable-next-line @next/next/no-img-element
          <img
            src={imageUrl}
            alt={analysis.title}
            className="w-full h-full object-contain"
          />
        ) : (
          <div className="w-full h-full flex items-center justify-center">
            <Shirt className="w-16 h-16 text-sand-300" />
          </div>
        )}

        {/* Versatility badge */}
        <div className="absolute top-3 right-3 bg-white/90 backdrop-blur-sm rounded-full px-3 py-1 flex items-center gap-1 text-sm font-semibold text-ink shadow-sm">
          <Star size={13} className="text-camel-400 fill-camel-400" />
          {analysis.versatilityScore}/10
        </div>
      </div>

      {/* Header */}
      <div className="flex items-start justify-between mb-2">
        <div>
          <h1 className="text-2xl font-bold text-ink leading-tight">{analysis.title}</h1>
          <p className="text-sm text-[#6B6B6E] mt-1 flex items-center gap-1.5">
            <Calendar size={13} />
            {formatDate(outfit.wornDate)}
            {outfit.source === 'exif' && (
              <span className="bg-forest-600 text-white text-[10px] px-1.5 py-0.5 rounded-full">
                from photo
              </span>
            )}
          </p>
        </div>
        <button
          onClick={handleDelete}
          disabled={deleting}
          className="p-2 rounded-xl hover:bg-red-50 text-[#6B6B6E] hover:text-red-500 transition-colors"
          title="Delete outfit"
        >
          <Trash2 size={18} />
        </button>
      </div>

      {/* Style + mood chips */}
      <div className="flex flex-wrap gap-2 mb-6">
        <span className="bg-forest-600 text-white text-xs font-medium px-3 py-1 rounded-full flex items-center gap-1">
          <Sparkles size={11} />
          {analysis.style}
        </span>
        <span className="bg-camel-400 text-white text-xs font-medium px-3 py-1 rounded-full">
          {analysis.mood}
        </span>
        {analysis.occasions.map((o) => (
          <span key={o} className="bg-sand-100 text-ink text-xs px-3 py-1 rounded-full">
            {OCCASION_LABEL[o] ?? o}
          </span>
        ))}
        {analysis.seasons.map((s) => (
          <span key={s} className="bg-sand-100 text-ink text-xs px-3 py-1 rounded-full">
            {SEASON_LABEL[s] ?? s}
          </span>
        ))}
      </div>

      {/* Description */}
      <p className="text-[#1C1C1E] leading-relaxed mb-8">{analysis.description}</p>

      {/* Confidence */}
      {analysis.confidence && (
        <div className="bg-sand-50 border border-sand-200 rounded-xl p-4 mb-8 flex gap-3">
          <Sparkles size={18} className="text-camel-400 flex-shrink-0 mt-0.5" />
          <p className="text-sm text-ink italic">&ldquo;{analysis.confidence}&rdquo;</p>
        </div>
      )}

      {/* Color palette */}
      <section className="mb-8">
        <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider mb-3 flex items-center gap-2">
          <Palette size={14} />
          Color Palette
        </h2>
        <div className="flex flex-wrap gap-3">
          {analysis.colors.map((color, i) => (
            <div key={i} className="flex items-center gap-2 bg-white rounded-xl px-3 py-2 border border-sand-200 shadow-sm">
              <div
                className="w-7 h-7 rounded-lg shadow-inner border border-black/10 flex-shrink-0"
                style={{ backgroundColor: color.hex }}
              />
              <div>
                <p className="text-xs font-medium text-ink leading-none">{color.name}</p>
                <p className="text-[10px] text-[#6B6B6E] mt-0.5">{color.percentage}%</p>
              </div>
            </div>
          ))}
        </div>
      </section>

      {/* Clothing items */}
      <section className="mb-8">
        <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider mb-3 flex items-center gap-2">
          <Tag size={14} />
          What You&apos;re Wearing
        </h2>
        <div className="grid grid-cols-1 sm:grid-cols-2 gap-3">
          {analysis.items.map((item, i) => (
            <div key={i} className="bg-white rounded-xl p-4 border border-sand-200 shadow-sm">
              <div className="flex items-center gap-2 mb-1">
                <span className="text-lg">{CATEGORY_EMOJI[item.category]}</span>
                <p className="text-sm font-semibold text-ink">{item.name}</p>
              </div>
              {(item.fabric || item.color) && (
                <p className="text-xs text-[#6B6B6E] ml-7">
                  {[item.color, item.fabric].filter(Boolean).join(' · ')}
                </p>
              )}
            </div>
          ))}
        </div>
      </section>

      {/* Style tips */}
      <section className="mb-8">
        <h2 className="text-sm font-semibold text-[#6B6B6E] uppercase tracking-wider mb-3 flex items-center gap-2">
          <Lightbulb size={14} />
          Style Tips
        </h2>
        <ul className="space-y-3">
          {analysis.tips.map((tip, i) => (
            <li key={i} className="flex gap-3 bg-white rounded-xl p-4 border border-sand-200 shadow-sm">
              <span className="flex-shrink-0 w-6 h-6 rounded-full bg-camel-400 text-white text-xs font-bold flex items-center justify-center">
                {i + 1}
              </span>
              <p className="text-sm text-ink leading-relaxed">{tip}</p>
            </li>
          ))}
        </ul>
      </section>

      {/* Actions */}
      <div className="flex gap-3 mt-4">
        <Link
          href="/upload"
          className="flex-1 bg-forest-600 text-white py-3 rounded-xl font-semibold text-center hover:bg-forest-700 transition-colors flex items-center justify-center gap-2"
        >
          <Sparkles size={16} />
          Add another outfit
        </Link>
        <Link
          href="/wardrobe"
          className="flex-1 bg-sand-100 text-ink py-3 rounded-xl font-semibold text-center hover:bg-sand-200 transition-colors"
        >
          View wardrobe
        </Link>
      </div>
    </div>
  );
}
