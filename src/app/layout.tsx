import type { Metadata } from 'next';
import './globals.css';
import Navigation from '@/components/Navigation';

export const metadata: Metadata = {
  title: 'Wardrobe AI — Your Personal Style Assistant',
  description: 'Upload your outfits, discover your style, and get AI-powered combination ideas.',
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>
        <Navigation />
        <main className="min-h-screen pb-24 md:pb-0 md:pl-60">
          {children}
        </main>
      </body>
    </html>
  );
}
