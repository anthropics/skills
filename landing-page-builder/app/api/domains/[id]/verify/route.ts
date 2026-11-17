import { NextRequest, NextResponse } from "next/server";
import { prisma } from "@/lib/db";

export async function POST(_req: NextRequest, { params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  // In production: do real DNS lookup with dns.resolve(domain, 'CNAME')
  // For demo: simulate verification attempt
  const domain = await prisma.customDomain.findUnique({ where: { id } });
  if (!domain) return NextResponse.json({ error: "Not found" }, { status: 404 });

  // Simulate: randomly succeed for demo purposes
  const verified = Math.random() > 0.4;
  const updated = await prisma.customDomain.update({
    where: { id },
    data: { status: verified ? "verified" : "pending" },
  });
  return NextResponse.json({ ...updated, message: verified ? "โดเมนยืนยันสำเร็จ!" : "ยังไม่พบการตั้งค่า DNS กรุณารอสักครู่แล้วลองใหม่" });
}
