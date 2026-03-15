'use client';

/**
 * Extracts the capture date from an image file's EXIF metadata.
 * Falls back to today's date if no EXIF date is found.
 */
export async function extractDateFromImage(file: File): Promise<{
  date: string;       // ISO YYYY-MM-DD
  source: 'exif' | 'manual';
}> {
  try {
    // Dynamic import so this only runs in the browser
    const exifr = await import('exifr');
    const tags = await exifr.parse(file, ['DateTimeOriginal', 'CreateDate', 'DateTime']);

    const raw: Date | string | undefined =
      tags?.DateTimeOriginal ?? tags?.CreateDate ?? tags?.DateTime;

    if (raw) {
      const d = raw instanceof Date ? raw : new Date(raw);
      if (!isNaN(d.getTime())) {
        return {
          date: d.toISOString().split('T')[0],
          source: 'exif',
        };
      }
    }
  } catch {
    // EXIF parsing failed; use today
  }

  return {
    date: new Date().toISOString().split('T')[0],
    source: 'manual',
  };
}

/** Format a date string (YYYY-MM-DD) for display. */
export function formatDate(dateStr: string): string {
  const d = new Date(dateStr + 'T12:00:00'); // noon to avoid TZ shift
  return d.toLocaleDateString('en-US', {
    weekday: 'long',
    year: 'numeric',
    month: 'long',
    day: 'numeric',
  });
}

export function formatDateShort(dateStr: string): string {
  const d = new Date(dateStr + 'T12:00:00');
  return d.toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' });
}

export function todayISO(): string {
  return new Date().toISOString().split('T')[0];
}

export function daysAgo(dateStr: string): number {
  const then = new Date(dateStr + 'T12:00:00').getTime();
  const now = Date.now();
  return Math.floor((now - then) / 86_400_000);
}
