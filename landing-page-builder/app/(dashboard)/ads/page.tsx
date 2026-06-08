"use client";

import { useState, useEffect } from "react";

interface AdPixel {
  id: string;
  name: string;
  type: string;
  pixelId: string;
  createdAt: string;
}

const AD_TYPES = [
  { value: "meta", label: "Meta (Facebook) Pixel", icon: "📘" },
  { value: "google", label: "Google Analytics / Ads", icon: "🔴" },
  { value: "tiktok", label: "TikTok Pixel", icon: "🎵" },
  { value: "custom", label: "Custom Script", icon: "⚙️" },
];

export default function AdsPage() {
  const [pixels, setPixels] = useState<AdPixel[]>([]);
  const [loading, setLoading] = useState(true);
  const [showForm, setShowForm] = useState(false);
  const [form, setForm] = useState({ name: "", type: "meta", pixelId: "", code: "" });
  const [saving, setSaving] = useState(false);

  useEffect(() => { fetchPixels(); }, []);

  async function fetchPixels() {
    const res = await fetch("/api/ads");
    setPixels(await res.json());
    setLoading(false);
  }

  async function savePixel() {
    if (!form.name || !form.pixelId) return;
    setSaving(true);
    await fetch("/api/ads", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(form),
    });
    setForm({ name: "", type: "meta", pixelId: "", code: "" });
    setShowForm(false);
    setSaving(false);
    fetchPixels();
  }

  async function deletePixel(id: string) {
    if (!confirm("ลบ pixel นี้?")) return;
    await fetch(`/api/ads/${id}`, { method: "DELETE" });
    setPixels((prev) => prev.filter((p) => p.id !== id));
  }

  const typeInfo = (type: string) => AD_TYPES.find((t) => t.value === type) ?? { icon: "⚙️", label: type };

  return (
    <div className="max-w-3xl">
      <div className="flex items-center justify-between mb-6">
        <div>
          <h2 className="text-2xl font-bold text-slate-800">Ads & Pixel Tracking</h2>
          <p className="text-sm text-slate-500 mt-1">จัดการ Pixel Tracking สำหรับโฆษณาบน Facebook, Google และอื่นๆ</p>
        </div>
        <button
          onClick={() => setShowForm(true)}
          className="bg-indigo-600 hover:bg-indigo-700 text-white px-4 py-2 rounded-lg text-sm font-medium"
        >
          + เพิ่ม Pixel
        </button>
      </div>

      {/* Info cards */}
      <div className="grid grid-cols-2 gap-4 mb-6">
        {AD_TYPES.slice(0, 4).map((t) => (
          <div key={t.value} className="bg-white rounded-xl border border-slate-200 p-4 flex items-center gap-3">
            <span className="text-2xl">{t.icon}</span>
            <div>
              <p className="text-sm font-semibold text-slate-700">{t.label}</p>
              <p className="text-xs text-slate-400">รองรับ</p>
            </div>
          </div>
        ))}
      </div>

      {/* Pixel list */}
      {loading ? (
        <div className="text-center py-10 text-slate-400">กำลังโหลด...</div>
      ) : pixels.length === 0 && !showForm ? (
        <div className="text-center py-16 border-2 border-dashed border-slate-200 rounded-xl">
          <p className="text-4xl mb-3">📣</p>
          <p className="text-slate-500 font-medium">ยังไม่มี Pixel</p>
          <p className="text-slate-400 text-sm mt-1">เพิ่ม Pixel เพื่อติดตามผลโฆษณา</p>
          <button
            onClick={() => setShowForm(true)}
            className="mt-4 bg-indigo-600 hover:bg-indigo-700 text-white px-5 py-2 rounded-lg text-sm font-medium"
          >
            + เพิ่ม Pixel แรก
          </button>
        </div>
      ) : (
        <div className="space-y-3">
          {pixels.map((pixel) => {
            const info = typeInfo(pixel.type);
            return (
              <div key={pixel.id} className="bg-white rounded-xl border border-slate-200 p-4">
                <div className="flex items-center justify-between">
                  <div className="flex items-center gap-3">
                    <span className="text-2xl">{info.icon}</span>
                    <div>
                      <p className="font-semibold text-slate-800">{pixel.name}</p>
                      <p className="text-xs text-slate-400">{info.label}</p>
                      <p className="text-xs font-mono text-slate-500 mt-0.5">ID: {pixel.pixelId}</p>
                    </div>
                  </div>
                  <button
                    onClick={() => deletePixel(pixel.id)}
                    className="text-xs border border-red-200 hover:bg-red-50 text-red-500 px-3 py-1.5 rounded-md"
                  >
                    ลบ
                  </button>
                </div>
              </div>
            );
          })}
        </div>
      )}

      {/* Add pixel form */}
      {showForm && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <div className="bg-white rounded-2xl shadow-xl p-6 w-full max-w-md mx-4">
            <h3 className="text-lg font-bold text-slate-800 mb-5">เพิ่ม Pixel ใหม่</h3>

            <div className="mb-4">
              <label className="block text-sm font-medium text-slate-700 mb-1.5">ชื่อ (เพื่อจำ)</label>
              <input
                type="text"
                value={form.name}
                onChange={(e) => setForm((f) => ({ ...f, name: e.target.value }))}
                placeholder="เช่น Facebook Pixel - โปรโมชั่น A"
                className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-500"
              />
            </div>

            <div className="mb-4">
              <label className="block text-sm font-medium text-slate-700 mb-1.5">ประเภท</label>
              <div className="grid grid-cols-2 gap-2">
                {AD_TYPES.map((t) => (
                  <button
                    key={t.value}
                    onClick={() => setForm((f) => ({ ...f, type: t.value }))}
                    className={`flex items-center gap-2 border rounded-lg px-3 py-2 text-sm transition-colors ${
                      form.type === t.value
                        ? "border-indigo-500 bg-indigo-50 text-indigo-700"
                        : "border-slate-200 text-slate-600 hover:border-slate-300"
                    }`}
                  >
                    <span>{t.icon}</span>
                    <span className="text-xs font-medium truncate">{t.label.split(" ")[0]}</span>
                  </button>
                ))}
              </div>
            </div>

            <div className="mb-4">
              <label className="block text-sm font-medium text-slate-700 mb-1.5">
                {form.type === "meta" ? "Facebook Pixel ID" : form.type === "google" ? "Measurement ID (G-XXXXXXXX)" : form.type === "tiktok" ? "TikTok Pixel ID" : "Script ID / Name"}
              </label>
              <input
                type="text"
                value={form.pixelId}
                onChange={(e) => setForm((f) => ({ ...f, pixelId: e.target.value }))}
                placeholder={form.type === "meta" ? "123456789012345" : form.type === "google" ? "G-XXXXXXXXXX" : "Pixel ID"}
                className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-500 font-mono"
              />
            </div>

            {form.type === "custom" && (
              <div className="mb-4">
                <label className="block text-sm font-medium text-slate-700 mb-1.5">Custom JavaScript Code</label>
                <textarea
                  value={form.code}
                  onChange={(e) => setForm((f) => ({ ...f, code: e.target.value }))}
                  rows={4}
                  placeholder="// วาง JavaScript ที่นี่"
                  className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm font-mono focus:outline-none focus:ring-2 focus:ring-indigo-500 resize-none"
                />
              </div>
            )}

            <div className="flex gap-3 mt-5">
              <button onClick={() => setShowForm(false)} className="flex-1 border border-slate-200 text-slate-600 py-2 rounded-lg text-sm hover:bg-slate-50">
                ยกเลิก
              </button>
              <button
                onClick={savePixel}
                disabled={saving || !form.name || !form.pixelId}
                className="flex-1 bg-indigo-600 hover:bg-indigo-700 disabled:opacity-50 text-white py-2 rounded-lg text-sm font-medium"
              >
                {saving ? "กำลังบันทึก..." : "บันทึก Pixel"}
              </button>
            </div>
          </div>
        </div>
      )}

      {/* Guide section */}
      <div className="mt-8 bg-slate-50 rounded-xl p-5">
        <h3 className="font-semibold text-slate-700 mb-3 text-sm">📖 วิธีเชื่อม Pixel กับ Landing Page</h3>
        <ol className="text-sm text-slate-600 space-y-2 list-decimal list-inside">
          <li>เพิ่ม Pixel ด้านบนก่อน</li>
          <li>ไปที่ Page Builder → เปิดหน้า Landing Page</li>
          <li>ในแถบเครื่องมือ → แท็บ Ads (เร็วๆนี้)</li>
          <li>เลือก Pixel ที่ต้องการแนบกับหน้า</li>
          <li>Pixel จะถูกโหลดอัตโนมัติเมื่อผู้เยี่ยมชมเปิดหน้า</li>
        </ol>
      </div>
    </div>
  );
}
