"use client";

import { useState, useEffect } from "react";

interface Domain {
  id: string;
  domain: string;
  status: string;
  cnameTarget: string;
  createdAt: string;
  pages: { id: string; title: string; slug: string }[];
}

export default function DomainsPage() {
  const [domains, setDomains] = useState<Domain[]>([]);
  const [loading, setLoading] = useState(true);
  const [newDomain, setNewDomain] = useState("");
  const [adding, setAdding] = useState(false);
  const [verifying, setVerifying] = useState<string | null>(null);
  const [message, setMessage] = useState<{ id: string; text: string; ok: boolean } | null>(null);

  useEffect(() => { fetchDomains(); }, []);

  async function fetchDomains() {
    const res = await fetch("/api/domains");
    setDomains(await res.json());
    setLoading(false);
  }

  async function addDomain() {
    if (!newDomain.trim()) return;
    setAdding(true);
    const res = await fetch("/api/domains", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ domain: newDomain }),
    });
    if (res.ok) {
      setNewDomain("");
      fetchDomains();
    }
    setAdding(false);
  }

  async function verify(id: string) {
    setVerifying(id);
    const res = await fetch(`/api/domains/${id}/verify`, { method: "POST" });
    const data = await res.json();
    setMessage({ id, text: data.message, ok: data.status === "verified" });
    fetchDomains();
    setVerifying(null);
    setTimeout(() => setMessage(null), 5000);
  }

  async function deleteDomain(id: string) {
    if (!confirm("ลบโดเมนนี้?")) return;
    await fetch(`/api/domains/${id}`, { method: "DELETE" });
    setDomains((prev) => prev.filter((d) => d.id !== id));
  }

  const statusBadge = (status: string) => {
    const map: Record<string, string> = {
      verified: "bg-green-100 text-green-700",
      pending: "bg-amber-100 text-amber-700",
      failed: "bg-red-100 text-red-700",
    };
    const label: Record<string, string> = {
      verified: "✅ ยืนยันแล้ว",
      pending: "⏳ รอยืนยัน",
      failed: "❌ ล้มเหลว",
    };
    return (
      <span className={`text-xs px-2 py-0.5 rounded-full font-medium ${map[status] ?? "bg-slate-100 text-slate-500"}`}>
        {label[status] ?? status}
      </span>
    );
  };

  return (
    <div className="max-w-3xl">
      <div className="mb-6">
        <h2 className="text-2xl font-bold text-slate-800">จัดการโดเมน</h2>
        <p className="text-sm text-slate-500 mt-1">เชื่อมต่อโดเมนที่ซื้อมาแสดง Landing Page ของคุณ</p>
      </div>

      {/* How it works */}
      <div className="bg-indigo-50 border border-indigo-100 rounded-xl p-4 mb-6">
        <h3 className="font-semibold text-indigo-800 mb-2 text-sm">📌 วิธีตั้งค่าโดเมน</h3>
        <ol className="text-sm text-indigo-700 space-y-1 list-decimal list-inside">
          <li>เพิ่มโดเมนของคุณด้านล่าง</li>
          <li>ไปที่ผู้ให้บริการโดเมน (เช่น Cloudflare, GoDaddy) แล้วสร้าง CNAME record</li>
          <li>ตั้งค่า CNAME ชี้ไปที่ <code className="bg-indigo-100 px-1 rounded font-mono text-xs">landing.pagebuilder.app</code></li>
          <li>กดปุ่ม "ยืนยัน DNS" หลังจากตั้งค่าเสร็จ (อาจใช้เวลา 5-60 นาที)</li>
        </ol>
      </div>

      {/* Add domain form */}
      <div className="bg-white rounded-xl border border-slate-200 p-5 mb-6">
        <h3 className="font-semibold text-slate-700 mb-3 text-sm">เพิ่มโดเมนใหม่</h3>
        <div className="flex gap-3">
          <input
            type="text"
            value={newDomain}
            onChange={(e) => setNewDomain(e.target.value)}
            onKeyDown={(e) => e.key === "Enter" && addDomain()}
            placeholder="เช่น shop.example.com หรือ promo.mybrand.co.th"
            className="flex-1 border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-500"
          />
          <button
            onClick={addDomain}
            disabled={adding || !newDomain.trim()}
            className="bg-indigo-600 hover:bg-indigo-700 disabled:opacity-50 text-white px-4 py-2 rounded-lg text-sm font-medium"
          >
            {adding ? "กำลังเพิ่ม..." : "เพิ่มโดเมน"}
          </button>
        </div>
      </div>

      {/* Domain list */}
      {loading ? (
        <div className="text-center py-10 text-slate-400">กำลังโหลด...</div>
      ) : domains.length === 0 ? (
        <div className="text-center py-16 border-2 border-dashed border-slate-200 rounded-xl">
          <p className="text-4xl mb-3">🌐</p>
          <p className="text-slate-500 font-medium">ยังไม่มีโดเมน</p>
          <p className="text-slate-400 text-sm mt-1">เพิ่มโดเมนของคุณด้านบน</p>
        </div>
      ) : (
        <div className="space-y-3">
          {domains.map((domain) => (
            <div key={domain.id} className="bg-white rounded-xl border border-slate-200 p-5">
              <div className="flex items-start justify-between gap-4">
                <div className="flex-1 min-w-0">
                  <div className="flex items-center gap-3 flex-wrap">
                    <span className="font-semibold text-slate-800">{domain.domain}</span>
                    {statusBadge(domain.status)}
                  </div>
                  <div className="mt-2 text-xs text-slate-500 space-y-1">
                    <p>
                      CNAME: <code className="bg-slate-100 px-1.5 py-0.5 rounded font-mono">{domain.domain}</code>
                      {" → "}
                      <code className="bg-slate-100 px-1.5 py-0.5 rounded font-mono">{domain.cnameTarget}</code>
                    </p>
                    {domain.pages.length > 0 && (
                      <p>ใช้กับ: {domain.pages.map((p) => p.title).join(", ")}</p>
                    )}
                  </div>
                  {message?.id === domain.id && (
                    <div className={`mt-2 text-xs px-3 py-1.5 rounded-lg ${message.ok ? "bg-green-50 text-green-700" : "bg-amber-50 text-amber-700"}`}>
                      {message.text}
                    </div>
                  )}
                </div>
                <div className="flex items-center gap-2 flex-shrink-0">
                  <button
                    onClick={() => verify(domain.id)}
                    disabled={verifying === domain.id}
                    className="text-xs border border-indigo-200 hover:border-indigo-400 text-indigo-600 hover:bg-indigo-50 px-3 py-1.5 rounded-md transition-colors"
                  >
                    {verifying === domain.id ? "กำลังตรวจสอบ..." : "ยืนยัน DNS"}
                  </button>
                  <button
                    onClick={() => deleteDomain(domain.id)}
                    className="text-xs border border-red-200 hover:bg-red-50 text-red-500 px-3 py-1.5 rounded-md transition-colors"
                  >
                    ลบ
                  </button>
                </div>
              </div>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
