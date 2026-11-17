"use client";

import { Block, BlockType, blockDefaults } from "@/lib/types";
import { nanoid } from "nanoid";

interface Props {
  block: Block | null;
  onUpdate: (updated: Block) => void;
  onClose: () => void;
}

function Field({
  label,
  value,
  onChange,
  multiline = false,
  type = "text",
}: {
  label: string;
  value: string;
  onChange: (v: string) => void;
  multiline?: boolean;
  type?: string;
}) {
  return (
    <div className="mb-4">
      <label className="block text-xs font-medium text-slate-600 mb-1">{label}</label>
      {multiline ? (
        <textarea
          value={value}
          onChange={(e) => onChange(e.target.value)}
          rows={3}
          className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-400 resize-none"
        />
      ) : (
        <input
          type={type}
          value={value}
          onChange={(e) => onChange(e.target.value)}
          className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-indigo-400"
        />
      )}
    </div>
  );
}

function updateContent(block: Block, key: string, value: unknown): Block {
  return { ...block, content: { ...block.content, [key]: value } };
}

export function BlockEditor({ block, onUpdate, onClose }: Props) {
  if (!block) return null;

  const c = block.content;
  const s = (key: string) => (c[key] as string) ?? "";

  const renderFields = () => {
    switch (block.type) {
      case "hero":
        return (
          <>
            <Field label="หัวข้อหลัก" value={s("heading")} onChange={(v) => onUpdate(updateContent(block, "heading", v))} />
            <Field label="คำอธิบาย" value={s("subheading")} onChange={(v) => onUpdate(updateContent(block, "subheading", v))} multiline />
            <Field label="ข้อความปุ่ม" value={s("buttonText")} onChange={(v) => onUpdate(updateContent(block, "buttonText", v))} />
            <Field label="ลิ้งก์ปุ่ม" value={s("buttonUrl")} onChange={(v) => onUpdate(updateContent(block, "buttonUrl", v))} />
            <Field label="URL รูป Background" value={s("backgroundImage")} onChange={(v) => onUpdate(updateContent(block, "backgroundImage", v))} />
          </>
        );

      case "features": {
        const items = (c.items as Array<{ icon: string; title: string; desc: string }>) ?? [];
        return (
          <>
            <Field label="หัวข้อส่วน" value={s("heading")} onChange={(v) => onUpdate(updateContent(block, "heading", v))} />
            <div className="mb-2">
              <label className="block text-xs font-medium text-slate-600 mb-2">รายการฟีเจอร์</label>
              {items.map((item, i) => (
                <div key={i} className="border border-slate-200 rounded-lg p-3 mb-2 space-y-2">
                  <div className="flex gap-2">
                    <input
                      className="w-16 border border-slate-200 rounded px-2 py-1 text-sm"
                      value={item.icon}
                      placeholder="ไอคอน"
                      onChange={(e) => {
                        const next = items.map((it, idx) => (idx === i ? { ...it, icon: e.target.value } : it));
                        onUpdate(updateContent(block, "items", next));
                      }}
                    />
                    <input
                      className="flex-1 border border-slate-200 rounded px-2 py-1 text-sm"
                      value={item.title}
                      placeholder="ชื่อ"
                      onChange={(e) => {
                        const next = items.map((it, idx) => (idx === i ? { ...it, title: e.target.value } : it));
                        onUpdate(updateContent(block, "items", next));
                      }}
                    />
                    <button
                      onClick={() => onUpdate(updateContent(block, "items", items.filter((_, idx) => idx !== i)))}
                      className="text-red-400 hover:text-red-600 text-sm px-1"
                    >
                      ✕
                    </button>
                  </div>
                  <input
                    className="w-full border border-slate-200 rounded px-2 py-1 text-sm"
                    value={item.desc}
                    placeholder="คำอธิบาย"
                    onChange={(e) => {
                      const next = items.map((it, idx) => (idx === i ? { ...it, desc: e.target.value } : it));
                      onUpdate(updateContent(block, "items", next));
                    }}
                  />
                </div>
              ))}
              <button
                onClick={() => onUpdate(updateContent(block, "items", [...items, { icon: "⭐", title: "หัวข้อ", desc: "คำอธิบาย" }]))}
                className="w-full border border-dashed border-indigo-300 text-indigo-500 text-sm py-1.5 rounded-lg hover:bg-indigo-50"
              >
                + เพิ่มรายการ
              </button>
            </div>
          </>
        );
      }

      case "text":
        return (
          <>
            <Field label="เนื้อหา" value={s("content")} onChange={(v) => onUpdate(updateContent(block, "content", v))} multiline />
            <div className="mb-4">
              <label className="block text-xs font-medium text-slate-600 mb-1">การจัดตำแหน่ง</label>
              <select
                value={s("align")}
                onChange={(e) => onUpdate(updateContent(block, "align", e.target.value))}
                className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm"
              >
                {["left", "center", "right"].map((v) => (
                  <option key={v} value={v}>{v === "left" ? "ซ้าย" : v === "center" ? "กลาง" : "ขวา"}</option>
                ))}
              </select>
            </div>
          </>
        );

      case "image":
        return (
          <>
            <Field label="URL รูปภาพ" value={s("src")} onChange={(v) => onUpdate(updateContent(block, "src", v))} />
            <Field label="Alt text" value={s("alt")} onChange={(v) => onUpdate(updateContent(block, "alt", v))} />
            <Field label="คำบรรยาย" value={s("caption")} onChange={(v) => onUpdate(updateContent(block, "caption", v))} />
          </>
        );

      case "cta":
        return (
          <>
            <Field label="หัวข้อ" value={s("heading")} onChange={(v) => onUpdate(updateContent(block, "heading", v))} />
            <Field label="คำอธิบาย" value={s("subheading")} onChange={(v) => onUpdate(updateContent(block, "subheading", v))} multiline />
            <Field label="ข้อความปุ่ม" value={s("buttonText")} onChange={(v) => onUpdate(updateContent(block, "buttonText", v))} />
            <Field label="ลิ้งก์ปุ่ม" value={s("buttonUrl")} onChange={(v) => onUpdate(updateContent(block, "buttonUrl", v))} />
            <Field label="สีพื้นหลัง" value={s("bgColor")} onChange={(v) => onUpdate(updateContent(block, "bgColor", v))} type="color" />
          </>
        );

      case "testimonial": {
        const items = (c.items as Array<{ quote: string; name: string; role: string; avatar: string }>) ?? [];
        return (
          <>
            {items.map((item, i) => (
              <div key={i} className="border border-slate-200 rounded-lg p-3 mb-2 space-y-2">
                <div className="flex justify-between items-center mb-1">
                  <span className="text-xs font-medium text-slate-500">รีวิวที่ {i + 1}</span>
                  <button onClick={() => onUpdate(updateContent(block, "items", items.filter((_, idx) => idx !== i)))} className="text-red-400 text-xs">ลบ</button>
                </div>
                {(["quote", "name", "role"] as const).map((field) => (
                  <input
                    key={field}
                    className="w-full border border-slate-200 rounded px-2 py-1 text-sm"
                    value={item[field]}
                    placeholder={field === "quote" ? "ข้อความรีวิว" : field === "name" ? "ชื่อ" : "ตำแหน่ง"}
                    onChange={(e) => {
                      const next = items.map((it, idx) => (idx === i ? { ...it, [field]: e.target.value } : it));
                      onUpdate(updateContent(block, "items", next));
                    }}
                  />
                ))}
              </div>
            ))}
            <button
              onClick={() => onUpdate(updateContent(block, "items", [...items, { quote: "รีวิวใหม่", name: "ชื่อลูกค้า", role: "ตำแหน่ง", avatar: "" }]))}
              className="w-full border border-dashed border-indigo-300 text-indigo-500 text-sm py-1.5 rounded-lg hover:bg-indigo-50"
            >
              + เพิ่มรีวิว
            </button>
          </>
        );
      }

      case "video":
        return (
          <>
            <Field label="URL วิดีโอ (YouTube embed)" value={s("url")} onChange={(v) => onUpdate(updateContent(block, "url", v))} />
            <Field label="ชื่อวิดีโอ" value={s("title")} onChange={(v) => onUpdate(updateContent(block, "title", v))} />
          </>
        );

      case "countdown":
        return (
          <>
            <Field label="หัวข้อ" value={s("heading")} onChange={(v) => onUpdate(updateContent(block, "heading", v))} />
            <Field label="วันเวลาสิ้นสุด" value={s("targetDate").split(".")[0]} onChange={(v) => onUpdate(updateContent(block, "targetDate", v))} type="datetime-local" />
            <Field label="ข้อความใต้นาฬิกา" value={s("subtext")} onChange={(v) => onUpdate(updateContent(block, "subtext", v))} />
          </>
        );

      case "form": {
        const fields = (c.fields as string[]) ?? [];
        return (
          <>
            <Field label="หัวข้อฟอร์ม" value={s("heading")} onChange={(v) => onUpdate(updateContent(block, "heading", v))} />
            <div className="mb-4">
              <label className="block text-xs font-medium text-slate-600 mb-2">ฟิลด์</label>
              {fields.map((field, i) => (
                <div key={i} className="flex gap-2 mb-2">
                  <input
                    className="flex-1 border border-slate-200 rounded px-2 py-1 text-sm"
                    value={field}
                    onChange={(e) => {
                      const next = fields.map((f, idx) => (idx === i ? e.target.value : f));
                      onUpdate(updateContent(block, "fields", next));
                    }}
                  />
                  <button onClick={() => onUpdate(updateContent(block, "fields", fields.filter((_, idx) => idx !== i)))} className="text-red-400 text-xs px-1">✕</button>
                </div>
              ))}
              <button
                onClick={() => onUpdate(updateContent(block, "fields", [...fields, "ฟิลด์ใหม่"]))}
                className="w-full border border-dashed border-indigo-300 text-indigo-500 text-sm py-1.5 rounded-lg hover:bg-indigo-50"
              >
                + เพิ่มฟิลด์
              </button>
            </div>
            <Field label="ข้อความปุ่มส่ง" value={s("buttonText")} onChange={(v) => onUpdate(updateContent(block, "buttonText", v))} />
          </>
        );
      }

      default:
        return <p className="text-slate-400 text-sm">ไม่มีการตั้งค่าสำหรับ block นี้</p>;
    }
  };

  return (
    <div className="flex flex-col h-full">
      <div className="flex items-center justify-between px-4 py-3 border-b border-slate-100">
        <div>
          <p className="text-xs text-slate-400 uppercase tracking-wide">แก้ไข Block</p>
          <p className="font-semibold text-slate-800 text-sm capitalize">{block.type}</p>
        </div>
        <button onClick={onClose} className="text-slate-400 hover:text-slate-600 text-lg">✕</button>
      </div>
      <div className="flex-1 overflow-y-auto px-4 py-4">{renderFields()}</div>
    </div>
  );
}

export function BlockPalette({ onAdd }: { onAdd: (type: BlockType) => void }) {
  const blocks: { type: BlockType; icon: string; label: string }[] = [
    { type: "hero", icon: "🦸", label: "Hero" },
    { type: "features", icon: "⭐", label: "Features" },
    { type: "text", icon: "📝", label: "Text" },
    { type: "image", icon: "🖼️", label: "Image" },
    { type: "cta", icon: "🎯", label: "CTA" },
    { type: "testimonial", icon: "💬", label: "รีวิว" },
    { type: "video", icon: "▶️", label: "Video" },
    { type: "countdown", icon: "⏱️", label: "นับถอยหลัง" },
    { type: "form", icon: "📋", label: "ฟอร์ม" },
    { type: "divider", icon: "➖", label: "เส้นคั่น" },
  ];

  return (
    <div className="px-4 py-4">
      <p className="text-xs font-medium text-slate-500 uppercase tracking-wide mb-3">เพิ่ม Block</p>
      <div className="grid grid-cols-2 gap-2">
        {blocks.map((b) => (
          <button
            key={b.type}
            onClick={() =>
              onAdd(b.type)
            }
            className="flex items-center gap-2 border border-slate-200 hover:border-indigo-300 hover:bg-indigo-50 rounded-lg px-3 py-2.5 text-sm text-slate-700 transition-colors text-left"
          >
            <span className="text-base">{b.icon}</span>
            <span className="font-medium text-xs">{b.label}</span>
          </button>
        ))}
      </div>
    </div>
  );
}

export function createBlock(type: BlockType): Block {
  return { id: nanoid(), type, content: { ...blockDefaults[type] } };
}
