import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";
import { nanoid } from "nanoid";

export async function GET() {
  const pages = await prisma.page.findMany({
    orderBy: { updatedAt: "desc" },
    include: { customDomain: true },
  });
  return NextResponse.json(pages);
}

export async function POST(req: NextRequest) {
  const { title } = await req.json();
  if (!title) return NextResponse.json({ error: "Title required" }, { status: 400 });

  const slug = title
    .toLowerCase()
    .replace(/[^a-z0-9ก-๙\s]/g, "")
    .replace(/\s+/g, "-")
    .slice(0, 50) + "-" + nanoid(6);

  const page = await prisma.page.create({
    data: { title, slug },
  });
  return NextResponse.json(page, { status: 201 });
}
