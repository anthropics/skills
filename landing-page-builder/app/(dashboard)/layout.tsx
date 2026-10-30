"use client";

import Link from "next/link";
import { usePathname } from "next/navigation";

const navItems = [
  { href: "/", icon: "🏠", label: "หน้าหลัก" },
  { href: "/domains", icon: "🌐", label: "โดเมน" },
  { href: "/ads", icon: "📣", label: "Ads & Pixel" },
];

export default function DashboardLayout({ children }: { children: React.ReactNode }) {
  const pathname = usePathname();

  return (
    <div className="flex h-screen bg-slate-50">
      {/* Sidebar */}
      <aside className="w-60 bg-white border-r border-slate-200 flex flex-col">
        <div className="px-6 py-5 border-b border-slate-100">
          <span className="text-xl font-bold text-indigo-600">PageCraft</span>
          <p className="text-xs text-slate-400 mt-0.5">Landing Page Builder</p>
        </div>
        <nav className="flex-1 px-3 py-4 space-y-1">
          {navItems.map((item) => (
            <Link
              key={item.href}
              href={item.href}
              className={`flex items-center gap-3 px-3 py-2 rounded-lg text-sm font-medium transition-colors ${
                pathname === item.href
                  ? "bg-indigo-50 text-indigo-700"
                  : "text-slate-600 hover:bg-slate-50 hover:text-slate-900"
              }`}
            >
              <span className="text-base">{item.icon}</span>
              {item.label}
            </Link>
          ))}
        </nav>
        <div className="px-4 py-4 border-t border-slate-100">
          <div className="bg-indigo-50 rounded-lg p-3 text-xs text-indigo-700">
            <p className="font-medium">ยังไม่ได้ upgrade</p>
            <p className="text-indigo-500 mt-1">Free plan: 3 หน้า</p>
          </div>
        </div>
      </aside>

      {/* Main content */}
      <div className="flex-1 flex flex-col overflow-hidden">
        <header className="bg-white border-b border-slate-200 px-6 py-3 flex items-center justify-between">
          <h1 className="text-sm font-medium text-slate-500">
            {pathname === "/" && "Dashboard"}
            {pathname === "/domains" && "จัดการโดเมน"}
            {pathname === "/ads" && "Ads & Pixel Tracking"}
            {pathname.startsWith("/builder") && "Page Builder"}
          </h1>
          <a
            href="#"
            className="text-xs bg-indigo-600 hover:bg-indigo-700 text-white px-3 py-1.5 rounded-md font-medium"
          >
            Upgrade Plan
          </a>
        </header>
        <main className="flex-1 overflow-y-auto p-6">{children}</main>
      </div>
    </div>
  );
}
