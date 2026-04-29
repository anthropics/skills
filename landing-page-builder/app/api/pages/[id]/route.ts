import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function GET(_req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const page = await prisma.page.findUnique({
    where: { id },
    include: { customDomain: true, pageAds: { include: { ad: true } } },
  });
  if (!page) return NextResponse.json({ error: "Not found" }, { status: 404 });
  return NextResponse.json(page);
}

export async function PATCH(req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const data = await req.json();
  const allowed = ["title", "blocks", "theme", "seoTitle", "seoDesc", "description", "customDomainId"];
  const update: Record<string, unknown> = {};
  for (const key of allowed) {
    if (key in data) {
      update[key] = typeof data[key] === "object" ? JSON.stringify(data[key]) : data[key];
    }
  }
  const page = await prisma.page.update({ where: { id }, data: update });
  return NextResponse.json(page);
}

export async function DELETE(_req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  await prisma.page.delete({ where: { id } });
  return NextResponse.json({ ok: true });
}
