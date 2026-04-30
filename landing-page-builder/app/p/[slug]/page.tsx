import { notFound } from "next/navigation";
import { prisma } from "@/lib/db";
import { Block, ThemeSettings, defaultTheme } from "@/lib/types";
import { BlockRenderer } from "@/components/builder/BlockRenderer";
import type { Metadata } from "next";

interface Props {
  params: Promise<{ slug: string }>;
}

async function getPage(slug: string) {
  return prisma.page.findUnique({
    where: { slug },
    include: { pageAds: { include: { ad: true } } },
  });
}

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const { slug } = await params;
  const page = await getPage(slug);
  if (!page) return { title: "Not Found" };
  return {
    title: page.seoTitle || page.title,
    description: page.seoDesc || page.description,
  };
}

export default async function PublicPage({ params }: Props) {
  const { slug } = await params;
  const page = await getPage(slug);

  if (!page || page.status !== "published") notFound();

  let blocks: Block[] = [];
  let theme: ThemeSettings = defaultTheme;
  try { blocks = JSON.parse(page.blocks); } catch { blocks = []; }
  try { theme = { ...defaultTheme, ...JSON.parse(page.theme) }; } catch { theme = defaultTheme; }

  const ads = page.pageAds.map((pa) => pa.ad);

  return (
    <>
      {/* Ad pixels in head-equivalent via script tags */}
      {ads.map((ad) => {
        if (ad.type === "meta") {
          return (
            <script
              key={ad.id}
              dangerouslySetInnerHTML={{
                __html: `
!function(f,b,e,v,n,t,s){if(f.fbq)return;n=f.fbq=function(){n.callMethod?n.callMethod.apply(n,arguments):n.queue.push(arguments)};if(!f._fbq)f._fbq=n;n.push=n;n.loaded=!0;n.version='2.0';n.queue=[];t=b.createElement(e);t.async=!0;t.src=v;s=b.getElementsByTagName(e)[0];s.parentNode.insertBefore(t,s)}(window,document,'script','https://connect.facebook.net/en_US/fbevents.js');fbq('init','${ad.pixelId}');fbq('track','PageView');
                `.trim(),
              }}
            />
          );
        }
        if (ad.type === "google") {
          return (
            <script
              key={ad.id}
              dangerouslySetInnerHTML={{
                __html: `window.dataLayer=window.dataLayer||[];function gtag(){dataLayer.push(arguments);}gtag('js',new Date());gtag('config','${ad.pixelId}');`,
              }}
            />
          );
        }
        if (ad.type === "custom" && ad.code) {
          return <script key={ad.id} dangerouslySetInnerHTML={{ __html: ad.code }} />;
        }
        return null;
      })}

      <div style={{ fontFamily: theme.fontFamily, backgroundColor: theme.backgroundColor, color: theme.textColor, minHeight: "100vh" }}>
        {blocks.map((block) => (
          <BlockRenderer key={block.id} block={block} theme={theme} isPreview={true} />
        ))}
        {blocks.length === 0 && (
          <div className="flex items-center justify-center min-h-screen text-slate-400">
            <p>หน้านี้ยังไม่มีเนื้อหา</p>
          </div>
        )}
      </div>
    </>
  );
}
