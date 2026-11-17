import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function POST(_req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const page = await prisma.page.update({
    where: { id },
    data: { status: "published" },
  });
  return NextResponse.json(page);
}

export async function DELETE(_req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const page = await prisma.page.update({
    where: { id },
    data: { status: "draft" },
  });
  return NextResponse.json(page);
}
