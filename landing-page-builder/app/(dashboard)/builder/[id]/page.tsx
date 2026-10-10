"use client";

import { useState, useEffect, useCallback, use } from "react";
import { useRouter } from "next/navigation";
import {
  DndContext,
  closestCenter,
  KeyboardSensor,
  PointerSensor,
  useSensor,
  useSensors,
  DragEndEvent,
} from "@dnd-kit/core";
import {
  arrayMove,
  SortableContext,
  sortableKeyboardCoordinates,
  useSortable,
  verticalListSortingStrategy,
} from "@dnd-kit/sortable";
import { CSS } from "@dnd-kit/utilities";
import { Block, ThemeSettings, defaultTheme, BlockType } from "@/lib/types";
import { BlockRenderer } from "@/components/builder/BlockRenderer";
import { BlockEditor, BlockPalette, createBlock } from "@/components/builder/BlockEditor";

interface PageData {
  id: string;
  title: string;
  slug: string;
  status: string;
  blocks: string;
  theme: string;
  seoTitle: string;
  seoDesc: string;
}

function SortableBlock({
  block,
  theme,
  isSelected,
  onClick,
  onDelete,
}: {
  block: Block;
  theme: ThemeSettings;
  isSelected: boolean;
  onClick: () => void;
  onDelete: () => void;
}) {
  const { attributes, listeners, setNodeRef, transform, transition, isDragging } = useSortable({ id: block.id });

  const style = {
    transform: CSS.Transform.toString(transform),
    transition,
    opacity: isDragging ? 0.5 : 1,
  };

  return (
    <div
      ref={setNodeRef}
      style={style}
      className={`builder-block group ${isSelected ? "selected" : ""}`}
      onClick={onClick}
    >
      {/* Toolbar overlay */}
      <div className="absolute top-1 right-1 z-10 hidden group-hover:flex items-center gap-1">
        <button
          className="drag-handle bg-white/90 border border-slate-200 text-slate-500 rounded px-2 py-1 text-xs shadow-sm"
          title="ลาก"
          {...attributes}
          {...listeners}
        >
          ⠿
        </button>
        <button
          onClick={(e) => { e.stopPropagation(); onDelete(); }}
          className="bg-white/90 border border-red-200 text-red-500 rounded px-2 py-1 text-xs shadow-sm hover:bg-red-50"
          title="ลบ"
        >
          🗑️
        </button>
      </div>
      <BlockRenderer block={block} theme={theme} isPreview={false} />
    </div>
  );
}

export default function BuilderPage({ params }: { params: Promise<{ id: string }> }) {
  const { id } = use(params);
  const router = useRouter();
  const [page, setPage] = useState<PageData | null>(null);
  const [blocks, setBlocks] = useState<Block[]>([]);
  const [theme, setTheme] = useState<ThemeSettings>(defaultTheme);
  const [selectedId, setSelectedId] = useState<string | null>(null);
  const [sidebarMode, setSidebarMode] = useState<"blocks" | "editor" | "theme" | "seo">("blocks");
  const [saving, setSaving] = useState(false);
  const [saved, setSaved] = useState(true);
  const [publishing, setPublishing] = useState(false);

  const sensors = useSensors(
    useSensor(PointerSensor),
    useSensor(KeyboardSensor, { coordinateGetter: sortableKeyboardCoordinates })
  );

  useEffect(() => {
    fetch(`/api/pages/${id}`)
      .then((r) => r.json())
      .then((data: PageData) => {
        setPage(data);
        try { setBlocks(JSON.parse(data.blocks)); } catch { setBlocks([]); }
        try { setTheme({ ...defaultTheme, ...JSON.parse(data.theme) }); } catch { setTheme(defaultTheme); }
      });
  }, [id]);

  const selectedBlock = blocks.find((b) => b.id === selectedId) ?? null;

  const save = useCallback(
    async (b: Block[], t: ThemeSettings) => {
      setSaving(true);
      await fetch(`/api/pages/${id}`, {
        method: "PATCH",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ blocks: b, theme: t }),
      });
      setSaving(false);
      setSaved(true);
    },
    [id]
  );

  useEffect(() => {
    if (!page) return;
    setSaved(false);
    const t = setTimeout(() => save(blocks, theme), 1500);
    return () => clearTimeout(t);
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [blocks, theme]);

  function handleDragEnd(event: DragEndEvent) {
    const { active, over } = event;
    if (over && active.id !== over.id) {
      setBlocks((items) => {
        const oldIndex = items.findIndex((i) => i.id === active.id);
        const newIndex = items.findIndex((i) => i.id === over.id);
        return arrayMove(items, oldIndex, newIndex);
      });
    }
  }

  function addBlock(type: BlockType) {
    const block = createBlock(type);
    setBlocks((prev) => [...prev, block]);
    setSelectedId(block.id);
    setSidebarMode("editor");
  }

  function updateBlock(updated: Block) {
    setBlocks((prev) => prev.map((b) => (b.id === updated.id ? updated : b)));
  }

  function deleteBlock(id: string) {
    setBlocks((prev) => prev.filter((b) => b.id !== id));
    if (selectedId === id) { setSelectedId(null); setSidebarMode("blocks"); }
  }

  async function togglePublish() {
    if (!page) return;
    setPublishing(true);
    await save(blocks, theme);
    const method = page.status === "published" ? "DELETE" : "POST";
    const res = await fetch(`/api/pages/${id}/publish`, { method });
    const updated = await res.json();
    setPage((p) => p ? { ...p, status: updated.status } : p);
    setPublishing(false);
  }

  if (!page) return <div className="flex items-center justify-center h-full text-slate-400">กำลังโหลด...</div>;

  const isPublished = page.status === "published";

  return (
    <div className="flex h-full -m-6 overflow-hidden">
      {/* Left Sidebar */}
      <div className="w-72 bg-white border-r border-slate-200 flex flex-col">
        {/* Sidebar tabs */}
        <div className="flex border-b border-slate-100">
          {(["blocks", "theme", "seo"] as const).map((tab) => (
            <button
              key={tab}
              onClick={() => { setSidebarMode(tab); setSelectedId(null); }}
              className={`flex-1 text-xs py-3 font-medium transition-colors ${sidebarMode === tab && !selectedId ? "text-indigo-600 border-b-2 border-indigo-500" : "text-slate-500 hover:text-slate-700"}`}
            >
              {tab === "blocks" ? "🧩 Blocks" : tab === "theme" ? "🎨 ธีม" : "🔍 SEO"}
            </button>
          ))}
        </div>

        <div className="flex-1 overflow-y-auto">
          {(selectedId && sidebarMode === "editor") ? (
            <BlockEditor
              block={selectedBlock}
              onUpdate={updateBlock}
              onClose={() => { setSelectedId(null); setSidebarMode("blocks"); }}
            />
          ) : sidebarMode === "blocks" ? (
            <BlockPalette onAdd={addBlock} />
          ) : sidebarMode === "theme" ? (
            <div className="px-4 py-4 space-y-4">
              <p className="text-xs font-medium text-slate-500 uppercase tracking-wide">ตั้งค่าธีม</p>
              {[
                { label: "สีหลัก", key: "primaryColor" },
                { label: "สีรอง", key: "secondaryColor" },
                { label: "สีพื้นหลัง", key: "backgroundColor" },
                { label: "สีข้อความ", key: "textColor" },
              ].map(({ label, key }) => (
                <div key={key}>
                  <label className="block text-xs font-medium text-slate-600 mb-1">{label}</label>
                  <div className="flex items-center gap-2">
                    <input
                      type="color"
                      value={theme[key as keyof ThemeSettings]}
                      onChange={(e) => setTheme((t) => ({ ...t, [key]: e.target.value }))}
                      className="w-10 h-10 rounded border border-slate-200 cursor-pointer"
                    />
                    <input
                      type="text"
                      value={theme[key as keyof ThemeSettings]}
                      onChange={(e) => setTheme((t) => ({ ...t, [key]: e.target.value }))}
                      className="flex-1 border border-slate-200 rounded px-2 py-1 text-sm font-mono"
                    />
                  </div>
                </div>
              ))}
              <div>
                <label className="block text-xs font-medium text-slate-600 mb-1">ฟอนต์</label>
                <select
                  value={theme.fontFamily}
                  onChange={(e) => setTheme((t) => ({ ...t, fontFamily: e.target.value }))}
                  className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm"
                >
                  {["Inter", "Sarabun", "Kanit", "Prompt", "Noto Sans Thai"].map((f) => (
                    <option key={f} value={f}>{f}</option>
                  ))}
                </select>
              </div>
            </div>
          ) : (
            <div className="px-4 py-4 space-y-4">
              <p className="text-xs font-medium text-slate-500 uppercase tracking-wide">SEO Settings</p>
              <div>
                <label className="block text-xs font-medium text-slate-600 mb-1">SEO Title</label>
                <input
                  type="text"
                  defaultValue={page.seoTitle}
                  onChange={(e) =>
                    fetch(`/api/pages/${id}`, { method: "PATCH", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ seoTitle: e.target.value }) })
                  }
                  className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm"
                />
              </div>
              <div>
                <label className="block text-xs font-medium text-slate-600 mb-1">SEO Description</label>
                <textarea
                  defaultValue={page.seoDesc}
                  onChange={(e) =>
                    fetch(`/api/pages/${id}`, { method: "PATCH", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ seoDesc: e.target.value }) })
                  }
                  rows={3}
                  className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm resize-none"
                />
              </div>
            </div>
          )}
        </div>
      </div>

      {/* Canvas */}
      <div className="flex-1 flex flex-col bg-slate-100 overflow-hidden">
        {/* Builder toolbar */}
        <div className="bg-white border-b border-slate-200 px-4 py-2 flex items-center justify-between gap-4">
          <button onClick={() => router.push("/")} className="text-slate-500 hover:text-slate-700 text-sm">← กลับ</button>
          <div className="flex items-center gap-1">
            <span className="text-sm font-medium text-slate-700 truncate max-w-[200px]">{page.title}</span>
            <span className={`text-xs px-2 py-0.5 rounded-full ml-2 ${isPublished ? "bg-green-100 text-green-700" : "bg-slate-100 text-slate-500"}`}>
              {isPublished ? "เผยแพร่แล้ว" : "ร่าง"}
            </span>
          </div>
          <div className="flex items-center gap-2">
            <span className="text-xs text-slate-400">{saving ? "⏳ กำลังบันทึก..." : saved ? "✅ บันทึกแล้ว" : ""}</span>
            {isPublished && (
              <a href={`/p/${page.slug}`} target="_blank" rel="noreferrer" className="text-xs border border-slate-200 hover:border-indigo-300 text-slate-600 hover:text-indigo-600 px-3 py-1.5 rounded-md">
                🔗 ดูหน้าจริง
              </a>
            )}
            <button
              onClick={togglePublish}
              disabled={publishing}
              className={`text-xs font-medium px-4 py-1.5 rounded-md transition-colors ${
                isPublished
                  ? "bg-amber-100 hover:bg-amber-200 text-amber-700"
                  : "bg-green-600 hover:bg-green-700 text-white"
              }`}
            >
              {publishing ? "..." : isPublished ? "🔒 ยกเลิกเผยแพร่" : "🚀 เผยแพร่"}
            </button>
          </div>
        </div>

        {/* Page canvas */}
        <div className="flex-1 overflow-y-auto">
          <div className="max-w-4xl mx-auto my-6 bg-white shadow-lg rounded-lg overflow-hidden min-h-96" style={{ fontFamily: theme.fontFamily }}>
            {blocks.length === 0 ? (
              <div className="py-24 text-center text-slate-300">
                <p className="text-5xl mb-4">✨</p>
                <p className="text-lg font-medium">เพิ่ม Block แรกของคุณ</p>
                <p className="text-sm mt-2">เลือก Block จากแถบซ้ายมือ</p>
              </div>
            ) : (
              <DndContext sensors={sensors} collisionDetection={closestCenter} onDragEnd={handleDragEnd}>
                <SortableContext items={blocks.map((b) => b.id)} strategy={verticalListSortingStrategy}>
                  {blocks.map((block) => (
                    <SortableBlock
                      key={block.id}
                      block={block}
                      theme={theme}
                      isSelected={selectedId === block.id}
                      onClick={() => { setSelectedId(block.id); setSidebarMode("editor"); }}
                      onDelete={() => deleteBlock(block.id)}
                    />
                  ))}
                </SortableContext>
              </DndContext>
            )}
          </div>
        </div>
      </div>
    </div>
  );
}
