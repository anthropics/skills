import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function POST(req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id: pageId } = await params;
  const { adId } = await req.json();
  try {
    const link = await prisma.pageAd.create({ data: { pageId, adId } });
    return NextResponse.json(link, { status: 201 });
  } catch {
    return NextResponse.json({ error: "Already linked" }, { status: 409 });
  }
}

export async function DELETE(req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id: pageId } = await params;
  const { adId } = await req.json();
  await prisma.pageAd.deleteMany({ where: { pageId, adId } });
  return NextResponse.json({ ok: true });
}
