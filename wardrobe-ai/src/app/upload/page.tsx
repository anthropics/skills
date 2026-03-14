'use client';

import { useState, useRef, useCallback, DragEvent } from 'react';
import { useRouter } from 'next/navigation';
import {
  Upload,
  Camera,
  Sparkles,
  CheckCircle,
  AlertCircle,
  ArrowRight,
  X,
} from 'lucide-react';
import { extractDateFromImage } from '@/lib/exif';
import { saveImage, generateId, createThumbnail } from '@/lib/storage';
import { saveOutfit } from '@/lib/storage';
import type { OutfitAnalysis } from '@/lib/types';

type Step = 'pick' | 'preview' | 'removing-bg' | 'confirm' | 'analyzing' | 'done' | 'error';

export default function UploadPage() {
  const router = useRouter();
  const fileInputRef = useRef<HTMLInputElement>(null);

  const [step, setStep] = useState<Step>('pick');
  const [originalFile, setOriginalFile] = useState<File | null>(null);
  const [processedBlob, setProcessedBlob] = useState<Blob | null>(null);
  const [previewUrl, setPreviewUrl] = useState<string | null>(null);
  const [processedUrl, setProcessedUrl] = useState<string | null>(null);
  const [wornDate, setWornDate] = useState<string>('');
  const [dateSource, setDateSource] = useState<'exif' | 'manual'>('manual');
  const [dragActive, setDragActive] = useState(false);
  const [errorMsg, setErrorMsg] = useState('');
  const [analysis, setAnalysis] = useState<OutfitAnalysis | null>(null);
  const [useOriginal, setUseOriginal] = useState(false);

  const processFile = useCallback(async (file: File) => {
    if (!file.type.startsWith('image/')) {
      setErrorMsg('Please upload an image file (JPEG, PNG, WebP).');
      setStep('error');
      return;
    }

    setOriginalFile(file);
    const url = URL.createObjectURL(file);
    setPreviewUrl(url);

    // Extract EXIF date
    const { date, source } = await extractDateFromImage(file);
    setWornDate(date);
    setDateSource(source);

    setStep('preview');
  }, []);

  const handleFiles = useCallback(
    async (files: FileList | null) => {
      if (!files || files.length === 0) return;
      await processFile(files[0]);
    },
    [processFile]
  );

  const handleDrop = useCallback(
    async (e: DragEvent<HTMLDivElement>) => {
      e.preventDefault();
      setDragActive(false);
      await handleFiles(e.dataTransfer.files);
    },
    [handleFiles]
  );

  const removeBackground = useCallback(async () => {
    if (!originalFile) return;
    setStep('removing-bg');

    try {
      // Dynamic import to avoid SSR issues with WASM
      const { removeBackground: removeBg } = await import('@imgly/background-removal');

      const resultBlob = await removeBg(originalFile, {
        // No publicPath — library fetches WASM/models from its own CDN
        progress: () => {},
        model: 'isnet_fp16',
      });

      const url = URL.createObjectURL(resultBlob);
      setProcessedBlob(resultBlob);
      setProcessedUrl(url);
      setUseOriginal(false);
      setStep('confirm');
    } catch (err) {
      console.error('Background removal failed:', err);
      // Fall back to original
      setUseOriginal(true);
      setStep('confirm');
    }
  }, [originalFile]);

  const skipBgRemoval = useCallback(() => {
    setUseOriginal(true);
    setStep('confirm');
  }, []);

  const analyzeOutfit = useCallback(async () => {
    if (!originalFile) return;
    setStep('analyzing');

    try {
      // Use processed (bg removed) or original
      const imageBlob = (!useOriginal && processedBlob) ? processedBlob : originalFile;

      // Convert to base64
      const arrayBuffer = await imageBlob.arrayBuffer();
      const base64 = Buffer.from(arrayBuffer).toString('base64');
      const mediaType = imageBlob.type || 'image/jpeg';

      // Call Claude API
      const res = await fetch('/api/analyze', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ imageBase64: base64, mediaType }),
      });

      if (!res.ok) {
        const err = await res.json();
        throw new Error(err.error || 'Analysis failed');
      }

      const { analysis: analysisResult } = await res.json();
      setAnalysis(analysisResult);

      // Save to storage
      const id = generateId();
      const imageKey = `${id}-image`;

      await saveImage(imageKey, imageBlob);
      const thumbnail = await createThumbnail(imageBlob);

      saveOutfit({
        id,
        wornDate,
        uploadedAt: new Date().toISOString(),
        analysis: analysisResult,
        imageKey,
        thumbnailDataUrl: thumbnail,
        source: dateSource,
      });

      setStep('done');
      setTimeout(() => {
        router.push(`/outfit/${id}`);
      }, 1500);
    } catch (err) {
      setErrorMsg(err instanceof Error ? err.message : 'Something went wrong. Please try again.');
      setStep('error');
    }
  }, [originalFile, processedBlob, useOriginal, wornDate, dateSource, router]);

  // ─── Render ───────────────────────────────────────────────────────────────

  if (step === 'pick') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 animate-fade-in">
        <div className="mb-8">
          <h1 className="text-2xl font-bold text-ink">Add an Outfit</h1>
          <p className="text-[#6B6B6E] mt-1">
            Upload a photo and let AI analyze your style, colors, and give you tips.
          </p>
        </div>

        {/* Drop zone */}
        <div
          className={`border-2 border-dashed rounded-2xl p-12 text-center transition-all cursor-pointer ${
            dragActive
              ? 'border-forest-600 bg-[#f0f7ef]'
              : 'border-sand-300 hover:border-sand-400 hover:bg-sand-50'
          }`}
          onDragOver={(e) => { e.preventDefault(); setDragActive(true); }}
          onDragLeave={() => setDragActive(false)}
          onDrop={handleDrop}
          onClick={() => fileInputRef.current?.click()}
        >
          <div className="flex flex-col items-center gap-4">
            <div className="w-16 h-16 bg-sand-100 rounded-2xl flex items-center justify-center">
              <Upload className="w-7 h-7 text-[#6B6B6E]" />
            </div>
            <div>
              <p className="font-semibold text-ink">Drop your photo here</p>
              <p className="text-sm text-[#6B6B6E] mt-1">or click to browse</p>
            </div>
            <p className="text-xs text-[#6B6B6E]">JPEG, PNG or WebP · Max 10 MB</p>
          </div>
        </div>

        {/* Camera button (mobile) */}
        <button
          className="w-full mt-4 flex items-center justify-center gap-2 py-3 border border-sand-200 rounded-xl text-sm font-medium text-[#6B6B6E] hover:bg-sand-50 transition-colors"
          onClick={() => {
            if (fileInputRef.current) {
              fileInputRef.current.accept = 'image/*';
              fileInputRef.current.capture = 'environment';
              fileInputRef.current.click();
            }
          }}
        >
          <Camera size={16} />
          Take a photo
        </button>

        <input
          ref={fileInputRef}
          type="file"
          accept="image/*"
          className="hidden"
          onChange={(e) => handleFiles(e.target.files)}
        />
      </div>
    );
  }

  if (step === 'preview') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 animate-fade-in">
        <h2 className="text-xl font-bold text-ink mb-6">Your photo</h2>

        <div className="rounded-2xl overflow-hidden bg-sand-100 aspect-[3/4] relative">
          {previewUrl && (
            // eslint-disable-next-line @next/next/no-img-element
            <img src={previewUrl} alt="Your outfit" className="w-full h-full object-cover" />
          )}
        </div>

        {/* Date */}
        <div className="mt-6 bg-white rounded-xl p-4 border border-sand-200">
          <label className="text-sm font-medium text-ink block mb-2">
            Date worn
            {dateSource === 'exif' && (
              <span className="ml-2 text-xs bg-forest-600 text-white px-2 py-0.5 rounded-full">
                from photo
              </span>
            )}
          </label>
          <input
            type="date"
            value={wornDate}
            onChange={(e) => { setWornDate(e.target.value); setDateSource('manual'); }}
            className="w-full px-3 py-2 rounded-lg border border-sand-200 text-sm focus:outline-none focus:ring-2 focus:ring-forest-600"
          />
        </div>

        <div className="mt-6 flex flex-col gap-3">
          <button
            onClick={removeBackground}
            className="w-full bg-forest-600 text-white py-3.5 rounded-xl font-semibold flex items-center justify-center gap-2 hover:bg-forest-700 transition-colors"
          >
            <Sparkles size={18} />
            Remove background & analyze
          </button>
          <button
            onClick={skipBgRemoval}
            className="w-full bg-sand-100 text-ink py-3.5 rounded-xl font-semibold hover:bg-sand-200 transition-colors text-sm"
          >
            Skip background removal
          </button>
        </div>

        <button
          onClick={() => { setStep('pick'); setPreviewUrl(null); }}
          className="mt-3 w-full text-sm text-[#6B6B6E] text-center hover:text-ink transition-colors"
        >
          Choose a different photo
        </button>
      </div>
    );
  }

  if (step === 'removing-bg') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 flex flex-col items-center justify-center min-h-[60vh] animate-fade-in">
        <div className="w-16 h-16 rounded-2xl bg-forest-600 flex items-center justify-center mb-6 animate-pulse">
          <Sparkles className="w-7 h-7 text-white" />
        </div>
        <h2 className="text-xl font-bold text-ink mb-2">Removing background…</h2>
        <p className="text-[#6B6B6E] text-sm text-center max-w-xs">
          Running AI background removal in your browser. This takes 5–15 seconds.
        </p>

        {previewUrl && (
          <div className="mt-8 w-40 h-56 rounded-xl overflow-hidden opacity-40 shimmer">
            {/* eslint-disable-next-line @next/next/no-img-element */}
            <img src={previewUrl} alt="" className="w-full h-full object-cover" />
          </div>
        )}
      </div>
    );
  }

  if (step === 'confirm') {
    const displayUrl = (!useOriginal && processedUrl) ? processedUrl : previewUrl;
    return (
      <div className="max-w-xl mx-auto px-4 py-12 animate-fade-in">
        <h2 className="text-xl font-bold text-ink mb-2">Looking good!</h2>
        <p className="text-[#6B6B6E] text-sm mb-6">
          {useOriginal
            ? 'Ready to analyze your outfit.'
            : 'Background removed. Ready for AI analysis.'}
        </p>

        <div className="rounded-2xl overflow-hidden bg-[#e8e3da] aspect-[3/4] relative">
          {displayUrl && (
            // eslint-disable-next-line @next/next/no-img-element
            <img
              src={displayUrl}
              alt="Your outfit"
              className="w-full h-full object-contain"
            />
          )}
        </div>

        <div className="mt-6 bg-white rounded-xl p-4 border border-sand-200">
          <div className="flex items-center justify-between">
            <div>
              <p className="text-sm font-medium text-ink">Date worn</p>
              <p className="text-sm text-[#6B6B6E] mt-0.5">{wornDate}</p>
            </div>
            <button
              onClick={() => setStep('preview')}
              className="text-xs text-forest-600 hover:underline"
            >
              Edit
            </button>
          </div>
        </div>

        <button
          onClick={analyzeOutfit}
          className="w-full mt-6 bg-forest-600 text-white py-3.5 rounded-xl font-semibold flex items-center justify-center gap-2 hover:bg-forest-700 transition-colors"
        >
          <Sparkles size={18} />
          Analyze my outfit
          <ArrowRight size={16} />
        </button>
      </div>
    );
  }

  if (step === 'analyzing') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 flex flex-col items-center justify-center min-h-[60vh] animate-fade-in">
        <div className="w-16 h-16 rounded-2xl bg-camel-400 flex items-center justify-center mb-6 animate-pulse">
          <Sparkles className="w-7 h-7 text-white" />
        </div>
        <h2 className="text-xl font-bold text-ink mb-2">Analyzing your style…</h2>
        <p className="text-[#6B6B6E] text-sm text-center max-w-xs">
          Claude is identifying your clothes, colors, and generating style insights.
        </p>

        <div className="mt-8 space-y-2 w-64">
          {['Identifying clothing items…', 'Reading color palette…', 'Writing style card…'].map(
            (label, i) => (
              <div
                key={i}
                className="h-3 rounded-full shimmer"
                style={{ width: `${100 - i * 12}%`, animationDelay: `${i * 0.3}s` }}
              />
            )
          )}
        </div>
      </div>
    );
  }

  if (step === 'done') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 flex flex-col items-center justify-center min-h-[60vh] animate-fade-in">
        <div className="w-16 h-16 rounded-2xl bg-forest-600 flex items-center justify-center mb-6">
          <CheckCircle className="w-8 h-8 text-white" />
        </div>
        <h2 className="text-xl font-bold text-ink mb-2">Outfit saved!</h2>
        <p className="text-[#6B6B6E] text-sm">Taking you to your style card…</p>
      </div>
    );
  }

  if (step === 'error') {
    return (
      <div className="max-w-xl mx-auto px-4 py-12 flex flex-col items-center justify-center min-h-[60vh] animate-fade-in">
        <div className="w-16 h-16 rounded-2xl bg-red-50 flex items-center justify-center mb-6">
          <AlertCircle className="w-8 h-8 text-red-500" />
        </div>
        <h2 className="text-xl font-bold text-ink mb-2">Something went wrong</h2>
        <p className="text-[#6B6B6E] text-sm text-center max-w-xs mb-6">{errorMsg}</p>
        <button
          onClick={() => { setStep('pick'); setErrorMsg(''); }}
          className="flex items-center gap-2 px-6 py-3 bg-forest-600 text-white rounded-xl font-medium hover:bg-forest-700 transition-colors"
        >
          <X size={16} />
          Try again
        </button>
      </div>
    );
  }

  return null;
}
