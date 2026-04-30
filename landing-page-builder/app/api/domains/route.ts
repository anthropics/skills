import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function GET() {
  const domains = await prisma.customDomain.findMany({
    orderBy: { createdAt: "desc" },
    include: { pages: { select: { id: true, title: true, slug: true } } },
  });
  return NextResponse.json(domains);
}

export async function POST(req: NextRequest) {
  const { domain } = await req.json();
  if (!domain) return NextResponse.json({ error: "Domain required" }, { status: 400 });

  const cleaned = domain.toLowerCase().trim().replace(/^https?:\/\//, "").replace(/\/$/, "");

  const existing = await prisma.customDomain.findUnique({ where: { domain: cleaned } });
  if (existing) return NextResponse.json({ error: "Domain already added" }, { status: 409 });

  const record = await prisma.customDomain.create({
    data: { domain: cleaned, cnameTarget: "landing.pagebuilder.app" },
  });
  return NextResponse.json(record, { status: 201 });
}
