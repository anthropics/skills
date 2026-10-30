"use client";

import { Block, ThemeSettings } from "@/lib/types";

interface Props {
  block: Block;
  theme: ThemeSettings;
  isPreview?: boolean;
}

function s(v: unknown): string { return (v as string) ?? ""; }

export function BlockRenderer({ block, theme, isPreview = false }: Props) {
  const c = block.content;

  switch (block.type) {
    case "hero":
      return (
        <div
          className="relative py-20 px-6 text-center"
          style={{
            backgroundImage: c.backgroundImage ? `url(${s(c.backgroundImage)})` : undefined,
            backgroundSize: "cover",
            backgroundPosition: "center",
            backgroundColor: c.backgroundImage ? undefined : theme.primaryColor,
            color: "#fff",
          }}
        >
          {!!c.backgroundImage && <div className="absolute inset-0 bg-black/50" />}
          <div className="relative max-w-3xl mx-auto">
            <h1 className="text-4xl font-bold leading-tight mb-4">{s(c.heading)}</h1>
            <p className="text-lg opacity-90 mb-8">{s(c.subheading)}</p>
            {!!c.buttonText && (
              <a
                href={s(c.buttonUrl)}
                className="inline-block px-8 py-3 rounded-full font-semibold text-sm transition-opacity hover:opacity-90"
                style={{ backgroundColor: theme.secondaryColor, color: "#fff" }}
                onClick={(e) => isPreview && e.preventDefault()}
              >
                {s(c.buttonText)}
              </a>
            )}
          </div>
        </div>
      );

    case "features": {
      const items = (c.items as Array<{ icon: string; title: string; desc: string }>) ?? [];
      return (
        <div className="py-16 px-6 bg-white">
          <div className="max-w-5xl mx-auto">
            {!!c.heading && (
              <h2 className="text-2xl font-bold text-center mb-10" style={{ color: theme.textColor }}>
                {s(c.heading)}
              </h2>
            )}
            <div className="grid grid-cols-1 md:grid-cols-3 gap-6">
              {items.map((item, i) => (
                <div key={i} className="text-center p-6 rounded-xl border border-slate-100 hover:shadow-md transition-shadow">
                  <div className="text-4xl mb-3">{item.icon}</div>
                  <h3 className="font-semibold text-slate-800 mb-1">{item.title}</h3>
                  <p className="text-sm text-slate-500">{item.desc}</p>
                </div>
              ))}
            </div>
          </div>
        </div>
      );
    }

    case "text":
      return (
        <div className="py-10 px-6">
          <div className="max-w-3xl mx-auto">
            <p
              className={`leading-relaxed text-${s(c.size)} text-${s(c.align)}`}
              style={{ color: theme.textColor }}
            >
              {s(c.content)}
            </p>
          </div>
        </div>
      );

    case "image":
      return (
        <div className="py-8 px-6">
          <div className={`mx-auto ${c.width === "full" ? "max-w-5xl" : "max-w-xl"}`}>
            {c.src ? (
              // eslint-disable-next-line @next/next/no-img-element
              <img src={s(c.src)} alt={s(c.alt)} className="w-full rounded-xl" />
            ) : (
              <div className="w-full h-48 bg-slate-100 rounded-xl flex items-center justify-center text-slate-400 text-sm">
                คลิกเพื่อเพิ่มรูปภาพ (ใส่ URL)
              </div>
            )}
            {!!c.caption && <p className="text-center text-sm text-slate-400 mt-2">{s(c.caption)}</p>}
          </div>
        </div>
      );

    case "cta":
      return (
        <div className="py-16 px-6 text-white text-center" style={{ backgroundColor: s(c.bgColor) || theme.primaryColor }}>
          <div className="max-w-2xl mx-auto">
            <h2 className="text-3xl font-bold mb-3">{s(c.heading)}</h2>
            <p className="text-lg opacity-90 mb-8">{s(c.subheading)}</p>
            <a
              href={s(c.buttonUrl)}
              className="inline-block bg-white font-semibold px-8 py-3 rounded-full text-sm transition-opacity hover:opacity-90"
              style={{ color: s(c.bgColor) || theme.primaryColor }}
              onClick={(e) => isPreview && e.preventDefault()}
            >
              {s(c.buttonText)}
            </a>
          </div>
        </div>
      );

    case "testimonial": {
      const testimonials = (c.items as Array<{ quote: string; name: string; role: string; avatar: string }>) ?? [];
      return (
        <div className="py-16 px-6 bg-slate-50">
          <div className="max-w-4xl mx-auto grid grid-cols-1 md:grid-cols-2 gap-6">
            {testimonials.map((t, i) => (
              <div key={i} className="bg-white rounded-xl p-6 shadow-sm">
                <p className="text-slate-700 mb-4 italic">&ldquo;{t.quote}&rdquo;</p>
                <div className="flex items-center gap-3">
                  <div className="w-10 h-10 rounded-full bg-indigo-100 flex items-center justify-center text-indigo-600 font-bold text-sm">
                    {t.name.charAt(0)}
                  </div>
                  <div>
                    <p className="font-semibold text-slate-800 text-sm">{t.name}</p>
                    <p className="text-xs text-slate-400">{t.role}</p>
                  </div>
                </div>
              </div>
            ))}
          </div>
        </div>
      );
    }

    case "video":
      return (
        <div className="py-12 px-6">
          <div className="max-w-3xl mx-auto">
            {!!c.title && <h2 className="text-xl font-bold text-center mb-4" style={{ color: theme.textColor }}>{s(c.title)}</h2>}
            <div className="relative pb-[56.25%] rounded-xl overflow-hidden bg-slate-100">
              <iframe
                src={s(c.url)}
                title={s(c.title)}
                className="absolute inset-0 w-full h-full"
                allowFullScreen
              />
            </div>
          </div>
        </div>
      );

    case "countdown":
      return (
        <div className="py-14 px-6 text-center" style={{ backgroundColor: theme.primaryColor, color: "#fff" }}>
          <h2 className="text-2xl font-bold mb-6">{s(c.heading)}</h2>
          <div className="flex justify-center gap-4">
            {["วัน", "ชั่วโมง", "นาที", "วินาที"].map((unit, i) => (
              <div key={i} className="bg-white/20 rounded-xl px-6 py-4 min-w-[72px]">
                <p className="text-3xl font-bold">00</p>
                <p className="text-xs opacity-80 mt-1">{unit}</p>
              </div>
            ))}
          </div>
          {!!c.subtext && <p className="mt-6 opacity-80">{s(c.subtext)}</p>}
        </div>
      );

    case "form": {
      const fields = (c.fields as string[]) ?? [];
      return (
        <div className="py-14 px-6">
          <div className="max-w-md mx-auto bg-white rounded-2xl shadow-md p-8">
            <h2 className="text-xl font-bold text-slate-800 mb-6 text-center">{s(c.heading)}</h2>
            <div className="space-y-4">
              {fields.map((field, i) => (
                <div key={i}>
                  <label className="block text-sm font-medium text-slate-700 mb-1">{field}</label>
                  <input
                    type="text"
                    placeholder={field}
                    className="w-full border border-slate-200 rounded-lg px-3 py-2 text-sm"
                    disabled={isPreview}
                  />
                </div>
              ))}
              <button
                className="w-full py-2.5 rounded-lg font-semibold text-white text-sm mt-2"
                style={{ backgroundColor: theme.primaryColor }}
              >
                {s(c.buttonText)}
              </button>
            </div>
          </div>
        </div>
      );
    }

    case "divider":
      return (
        <div className="py-4 px-6">
          <hr style={{ borderColor: s(c.color), borderStyle: s(c.style) as React.CSSProperties["borderStyle"] }} />
        </div>
      );

    default:
      return null;
  }
}
