import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "PageCraft — Landing Page Builder",
  description: "สร้าง Landing Page สวยงาม เผยแพร่ได้จริง จัดการโดเมนและ Ads ในที่เดียว",
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="th" className="h-full">
      <body className="min-h-full flex flex-col">{children}</body>
    </html>
  );
}
