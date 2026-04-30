"use client";

import { useState, useEffect } from "react";
import Link from "next/link";
import { useRouter } from "next/navigation";

interface Page {
  id: string;
  title: string;
  slug: string;
  status: string;
  updatedAt: string;
  customDomain?: { domain: string } | null;
}

export default function DashboardPage() {
  const router = useRouter();
  const [pages, setPages] = useState<Page[]>([]);
  const [loading, setLoading] = useState(true);
  const [creating, setCreating] = useState(false);
  const [newTitle, setNewTitle] = useState("");
  const [showModal, setShowModal] = useState(false);

  useEffect(() => {
    fetchPages();
  }, []);

  async function fetchPages() {
    const res = await fetch("/api/pages");
    const data = await res.json();
    setPages(data);
    setLoading(false);
  }

  async function createPage() {
    if (!newTitle.trim()) return;
    setCreating(true);
    const res = await fetch("/api/pages", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ title: newTitle }),
    });
    const page = await res.json();
    setCreating(false);
    setShowModal(false);
    setNewTitle("");
    router.push(`/builder/${page.id}`);
  }

  async function deletePage(id: string) {
    if (!confirm("ลบหน้านี้?")) return;
    await fetch(`/api/pages/${id}`, { method: "DELETE" });
    setPages((prev) => prev.filter((p) => p.id !== id));
  }

  async function togglePublish(page: Page) {
    const url = `/api/pages/${page.id}/publish`;
    const method = page.status === "published" ? "DELETE" : "POST";
    const res = await fetch(url, { method });
    const updated = await res.json();
    setPages((prev) => prev.map((p) => (p.id === updated.id ? { ...p, status: updated.status } : p)));
  }

  return (
    <div>
      {/* Header */}
      <div className="flex items-center justify-between mb-6">
        <div>
          <h2 className="text-2xl font-bold text-slate-800">Landing Pages ของคุณ</h2>
          <p className="text-sm text-slate-500 mt-1">สร้าง แก้ไข และเผยแพร่ landing page ของคุณ</p>
        </div>
        <button
          onClick={() => setShowModal(true)}
          className="flex items-center gap-2 bg-indigo-600 hover:bg-indigo-700 text-white px-4 py-2 rounded-lg text-sm font-medium transition-colors"
        >
          <span className="text-lg">+</span> สร้างหน้าใหม่
        </button>
      </div>

      {/* Stats */}
      <div className="grid grid-cols-3 gap-4 mb-8">
        {[
          { label: "หน้าทั้งหมด", value: pages.length, color: "bg-indigo-50 text-indigo-700" },
          { label: "เผยแพร่แล้ว", value: pages.filter((p) => p.status === "published").length, color: "bg-green-50 text-green-700" },
          { label: "ร่าง", value: pages.filter((p) => p.status === "draft").length, color: "bg-amber-50 text-amber-700" },
        ].map((stat) => (
          <div key={stat.label} className={`rounded-xl p-4 ${stat.color}`}>
            <p className="text-3xl font-bold">{stat.value}</p>
            <p className="text-sm mt-1 opacity-80">{stat.label}</p>
          </div>
        ))}
      </div>

      {/* Pages grid */}
      {loading ? (
        <div className="text-center py-16 text-slate-400">กำลังโหลด...</div>
      ) : pages.length === 0 ? (
        <div className="text-center py-20 border-2 border-dashed border-slate-200 rounded-2xl">
          <div className="text-6xl mb-4">📄</div>
          <h3 className="text-lg font-semibold text-slate-600">ยังไม่มี Landing Page</h3>
          <p className="text-slate-400 mt-2 mb-6">เริ่มสร้างหน้าแรกของคุณได้เลย</p>
          <button
            onClick={() => setShowModal(true)}
            className="bg-indigo-600 hover:bg-indigo-700 text-white px-5 py-2.5 rounded-lg text-sm font-medium"
          >
            + สร้างหน้าแรก
          </button>
        </div>
      ) : (
        <div className="grid grid-cols-1 md:grid-cols-2 xl:grid-cols-3 gap-4">
          {pages.map((page) => (
            <div
              key={page.id}
              className="bg-white rounded-xl border border-slate-200 hover:border-indigo-300 hover:shadow-md transition-all overflow-hidden"
            >
              {/* Preview thumbnail */}
              <div className="h-32 bg-gradient-to-br from-indigo-50 to-purple-50 flex items-center justify-center">
                <span className="text-4xl">🖥️</span>
              </div>

              <div className="p-4">
                <div className="flex items-start justify-between gap-2">
                  <div className="flex-1 min-w-0">
                    <h3 className="font-semibold text-slate-800 truncate">{page.title}</h3>
                    <p className="text-xs text-slate-400 mt-0.5 truncate">
                      {page.customDomain ? page.customDomain.domain : `/p/${page.slug}`}
                    </p>
                  </div>
                  <span
                    className={`flex-shrink-0 text-xs px-2 py-0.5 rounded-full font-medium ${
                      page.status === "published"
                        ? "bg-green-100 text-green-700"
                        : "bg-slate-100 text-slate-500"
                    }`}
                  >
                    {page.status === "published" ? "เผยแพร่แล้ว" : "ร่าง"}
                  </span>
                </div>

                <p className="text-xs text-slate-400 mt-2">
                  แก้ไขล่าสุด: {new Date(page.updatedAt).toLocaleDateString("th-TH")}
                </p>

                <div className="flex items-center gap-2 mt-3 pt-3 border-t border-slate-100">
                  <Link
                    href={`/builder/${page.id}`}
                    className="flex-1 text-center bg-indigo-50 hover:bg-indigo-100 text-indigo-700 text-xs font-medium py-1.5 rounded-md transition-colors"
                  >
                    ✏️ แก้ไข
                  </Link>
                  <button
                    onClick={() => togglePublish(page)}
                    className={`flex-1 text-xs font-medium py-1.5 rounded-md transition-colors ${
                      page.status === "published"
                        ? "bg-amber-50 hover:bg-amber-100 text-amber-700"
                        : "bg-green-50 hover:bg-green-100 text-green-700"
                    }`}
                  >
                    {page.status === "published" ? "🔒 ซ่อน" : "🚀 เผยแพร่"}
                  </button>
                  {page.status === "published" && (
                    <a
                      href={`/p/${page.slug}`}
                      target="_blank"
                      rel="noreferrer"
                      className="text-xs bg-slate-50 hover:bg-slate-100 text-slate-600 px-2 py-1.5 rounded-md transition-colors"
                      title="ดูหน้าจริง"
                    >
                      🔗
                    </a>
                  )}
                  <button
                    onClick={() => deletePage(page.id)}
                    className="text-xs bg-red-50 hover:bg-red-100 text-red-600 px-2 py-1.5 rounded-md transition-colors"
                    title="ลบ"
                  >
                    🗑️
                  </button>
                </div>
              </div>
            </div>
          ))}
        </div>
      )}

      {/* Create modal */}
      {showModal && (
        <div className="fixed inset-0 bg-black/50 flex items-center justify-center z-50">
          <div className="bg-white rounded-2xl shadow-xl p-6 w-full max-w-md mx-4">
            <h3 className="text-lg font-bold text-slate-800 mb-4">สร้าง Landing Page ใหม่</h3>
            <label className="block text-sm font-medium text-slate-700 mb-1.5">ชื่อหน้า</label>
            <input
              type="text"
              value={newTitle}
              onChange={(e) => setNewTitle(e.target.value)}
              onKeyDown={(e) => e.key === "Enter" && createPage()}
              placeholder="เช่น โปรโมชั่นเดือนนี้, สินค้า A"
              autoFocus
              className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-500"
            />
            <div className="flex gap-3 mt-5">
              <button
                onClick={() => setShowModal(false)}
                className="flex-1 border border-slate-200 text-slate-600 py-2 rounded-lg text-sm hover:bg-slate-50"
              >
                ยกเลิก
              </button>
              <button
                onClick={createPage}
                disabled={creating || !newTitle.trim()}
                className="flex-1 bg-indigo-600 hover:bg-indigo-700 disabled:opacity-50 text-white py-2 rounded-lg text-sm font-medium"
              >
                {creating ? "กำลังสร้าง..." : "สร้างและเปิด Builder"}
              </button>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
