'use client';

import { useState, useEffect } from 'react';
import Link from 'next/link';
import { ChevronLeft, ChevronRight, Plus, Sparkles } from 'lucide-react';
import { getAllOutfits } from '@/lib/storage';
import type { OutfitMeta } from '@/lib/types';
import { todayISO } from '@/lib/exif';

const DAYS_OF_WEEK = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
const MONTH_NAMES = [
  'January', 'February', 'March', 'April', 'May', 'June',
  'July', 'August', 'September', 'October', 'November', 'December',
];

function pad(n: number) {
  return String(n).padStart(2, '0');
}

function isoDate(year: number, month: number, day: number): string {
  return `${year}-${pad(month + 1)}-${pad(day)}`;
}

export default function CalendarPage() {
  const today = todayISO();
  const [current, setCurrent] = useState(() => {
    const d = new Date();
    return { year: d.getFullYear(), month: d.getMonth() };
  });
  const [outfits, setOutfits] = useState<OutfitMeta[]>([]);
  const [mounted, setMounted] = useState(false);

  useEffect(() => {
    setOutfits(getAllOutfits());
    setMounted(true);
    const handler = () => setOutfits(getAllOutfits());
    window.addEventListener('wardrobe-updated', handler);
    return () => window.removeEventListener('wardrobe-updated', handler);
  }, []);

  const { year, month } = current;

  // Build calendar grid
  const firstDayOfMonth = new Date(year, month, 1).getDay();
  const daysInMonth = new Date(year, month + 1, 0).getDate();

  // Index outfits by date
  const outfitsByDate = new Map<string, OutfitMeta[]>();
  for (const outfit of outfits) {
    const d = outfit.wornDate;
    if (!outfitsByDate.has(d)) outfitsByDate.set(d, []);
    outfitsByDate.get(d)!.push(outfit);
  }

  const prevMonth = () => {
    setCurrent((c) =>
      c.month === 0 ? { year: c.year - 1, month: 11 } : { year: c.year, month: c.month - 1 }
    );
  };
  const nextMonth = () => {
    setCurrent((c) =>
      c.month === 11 ? { year: c.year + 1, month: 0 } : { year: c.year, month: c.month + 1 }
    );
  };

  const monthPrefix = `${year}-${pad(month + 1)}`;
  let totalOutfitsThisMonth = 0;
  outfitsByDate.forEach((v, k) => {
    if (k.startsWith(monthPrefix)) totalOutfitsThisMonth += v.length;
  });

  if (!mounted) return null;

  return (
    <div className="max-w-2xl mx-auto px-4 py-8 animate-fade-in">
      {/* Header */}
      <div className="flex items-center justify-between mb-8">
        <div>
          <h1 className="text-2xl font-bold text-ink">Outfit Calendar</h1>
          {totalOutfitsThisMonth > 0 && (
            <p className="text-sm text-[#6B6B6E] mt-1">
              {totalOutfitsThisMonth} outfit{totalOutfitsThisMonth !== 1 ? 's' : ''} this month
            </p>
          )}
        </div>
        <Link
          href="/upload"
          className="flex items-center gap-1.5 bg-forest-600 text-white px-4 py-2 rounded-xl text-sm font-semibold hover:bg-forest-700 transition-colors"
        >
          <Plus size={16} />
          Add
        </Link>
      </div>

      {/* Month navigation */}
      <div className="flex items-center justify-between mb-6 bg-white rounded-xl p-3 border border-sand-200 shadow-sm">
        <button
          onClick={prevMonth}
          className="p-2 hover:bg-sand-100 rounded-lg transition-colors"
        >
          <ChevronLeft size={18} className="text-ink" />
        </button>
        <h2 className="font-semibold text-ink text-lg">
          {MONTH_NAMES[month]} {year}
        </h2>
        <button
          onClick={nextMonth}
          className="p-2 hover:bg-sand-100 rounded-lg transition-colors"
        >
          <ChevronRight size={18} className="text-ink" />
        </button>
      </div>

      {/* Day labels */}
      <div className="grid grid-cols-7 mb-2">
        {DAYS_OF_WEEK.map((d) => (
          <div key={d} className="text-center text-xs font-semibold text-[#6B6B6E] py-1">
            {d}
          </div>
        ))}
      </div>

      {/* Calendar grid */}
      <div className="grid grid-cols-7 gap-1">
        {/* Empty cells before first day */}
        {Array.from({ length: firstDayOfMonth }).map((_, i) => (
          <div key={`empty-${i}`} className="aspect-square" />
        ))}

        {/* Days */}
        {Array.from({ length: daysInMonth }).map((_, i) => {
          const day = i + 1;
          const dateStr = isoDate(year, month, day);
          const dayOutfits = outfitsByDate.get(dateStr) ?? [];
          const isToday = dateStr === today;
          const hasOutfits = dayOutfits.length > 0;

          return (
            <div
              key={day}
              className={`aspect-square rounded-xl relative overflow-hidden border transition-all ${
                isToday
                  ? 'border-forest-600 ring-2 ring-forest-600 ring-offset-1'
                  : hasOutfits
                  ? 'border-sand-200 hover:border-sand-300 cursor-pointer'
                  : 'border-transparent'
              }`}
            >
              {hasOutfits ? (
                // Show thumbnail of first outfit
                <Link href={`/outfit/${dayOutfits[0].id}`} className="block w-full h-full group">
                  {dayOutfits[0].thumbnailDataUrl ? (
                    // eslint-disable-next-line @next/next/no-img-element
                    <img
                      src={dayOutfits[0].thumbnailDataUrl}
                      alt=""
                      className="w-full h-full object-cover group-hover:scale-105 transition-transform duration-300"
                    />
                  ) : (
                    <div className="w-full h-full bg-sand-100 flex items-center justify-center">
                      <Sparkles size={14} className="text-[#6B6B6E]" />
                    </div>
                  )}

                  {/* Day number overlay */}
                  <div className="absolute top-1 left-1">
                    <span
                      className={`text-[10px] font-bold px-1 rounded ${
                        isToday ? 'bg-forest-600 text-white' : 'bg-white/80 text-ink'
                      }`}
                    >
                      {day}
                    </span>
                  </div>

                  {/* Multiple outfits badge */}
                  {dayOutfits.length > 1 && (
                    <div className="absolute bottom-1 right-1 bg-forest-600 text-white text-[10px] font-bold rounded-full w-4 h-4 flex items-center justify-center">
                      {dayOutfits.length}
                    </div>
                  )}
                </Link>
              ) : (
                // Empty day
                <Link href={`/upload`} className="block w-full h-full group">
                  <div
                    className={`w-full h-full flex items-center justify-center rounded-xl transition-colors ${
                      isToday
                        ? 'bg-forest-600/10'
                        : 'hover:bg-sand-50'
                    }`}
                  >
                    <span
                      className={`text-xs font-medium ${
                        isToday ? 'text-forest-600 font-bold' : 'text-[#6B6B6E]'
                      }`}
                    >
                      {day}
                    </span>
                  </div>
                </Link>
              )}
            </div>
          );
        })}
      </div>

      {/* Legend */}
      <div className="mt-6 flex items-center gap-4 text-xs text-[#6B6B6E]">
        <div className="flex items-center gap-1.5">
          <div className="w-3 h-3 rounded border-2 border-forest-600 ring-1 ring-forest-600 ring-offset-1" />
          Today
        </div>
        <div className="flex items-center gap-1.5">
          <div className="w-3 h-3 rounded bg-sand-100 border border-sand-200" />
          Outfit logged
        </div>
      </div>

      {/* Empty state */}
      {outfits.length === 0 && (
        <div className="mt-12 text-center">
          <p className="text-[#6B6B6E] text-sm mb-4">
            No outfits yet. Start uploading to fill your calendar!
          </p>
          <Link
            href="/upload"
            className="inline-flex items-center gap-2 bg-forest-600 text-white px-6 py-3 rounded-xl font-semibold hover:bg-forest-700 transition-colors"
          >
            <Plus size={16} />
            Upload first outfit
          </Link>
        </div>
      )}
    </div>
  );
}
