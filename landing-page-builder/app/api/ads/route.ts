import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function GET() {
  const ads = await prisma.adPixel.findMany({ orderBy: { createdAt: "desc" } });
  return NextResponse.json(ads);
}

export async function POST(req: NextRequest) {
  const { name, type, pixelId, code } = await req.json();
  if (!name || !type || !pixelId) return NextResponse.json({ error: "Missing fields" }, { status: 400 });
  const ad = await prisma.adPixel.create({ data: { name, type, pixelId, code: code ?? "" } });
  return NextResponse.json(ad, { status: 201 });
}
