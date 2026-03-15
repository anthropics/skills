'use client';

import Link from 'next/link';
import { usePathname } from 'next/navigation';
import { Home, Upload, Calendar, Layers, Sparkles } from 'lucide-react';

const links = [
  { href: '/', icon: Home, label: 'Morning' },
  { href: '/upload', icon: Upload, label: 'Upload' },
  { href: '/wardrobe', icon: Layers, label: 'Wardrobe' },
  { href: '/calendar', icon: Calendar, label: 'Calendar' },
];

export default function Navigation() {
  const pathname = usePathname();

  return (
    <>
      {/* Desktop sidebar */}
      <nav className="hidden md:flex fixed left-0 top-0 h-full w-60 bg-white border-r border-sand-200 flex-col py-8 px-4 z-40">
        {/* Logo */}
        <div className="flex items-center gap-2 px-2 mb-10">
          <div className="w-8 h-8 bg-forest-600 rounded-lg flex items-center justify-center">
            <Sparkles className="w-4 h-4 text-white" />
          </div>
          <span className="font-semibold text-ink text-lg tracking-tight">Wardrobe AI</span>
        </div>

        {/* Links */}
        <div className="flex flex-col gap-1">
          {links.map(({ href, icon: Icon, label }) => {
            const active = pathname === href || (href !== '/' && pathname.startsWith(href));
            return (
              <Link
                key={href}
                href={href}
                className={`flex items-center gap-3 px-3 py-2.5 rounded-xl text-sm font-medium transition-colors ${
                  active
                    ? 'bg-forest-600 text-white'
                    : 'text-[#6B6B6E] hover:bg-sand-100 hover:text-ink'
                }`}
              >
                <Icon className="w-4.5 h-4.5 flex-shrink-0" size={18} />
                {label}
              </Link>
            );
          })}
        </div>

        {/* Bottom hint */}
        <div className="mt-auto px-3 py-3 bg-sand-50 rounded-xl">
          <p className="text-xs text-[#6B6B6E] leading-relaxed">
            Upload outfits to discover your Style DNA and get combination ideas.
          </p>
        </div>
      </nav>

      {/* Mobile bottom bar */}
      <nav className="md:hidden fixed bottom-0 left-0 right-0 bg-white border-t border-sand-200 z-40 px-2 pb-safe">
        <div className="flex items-center justify-around h-16">
          {links.map(({ href, icon: Icon, label }) => {
            const active = pathname === href || (href !== '/' && pathname.startsWith(href));
            return (
              <Link
                key={href}
                href={href}
                className={`flex flex-col items-center gap-1 px-4 py-2 rounded-xl transition-colors ${
                  active ? 'text-forest-600' : 'text-[#6B6B6E]'
                }`}
              >
                <Icon size={20} />
                <span className="text-[10px] font-medium">{label}</span>
              </Link>
            );
          })}
        </div>
      </nav>
    </>
  );
}
