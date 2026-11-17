export type BlockType =
  | "hero"
  | "features"
  | "text"
  | "image"
  | "cta"
  | "testimonial"
  | "video"
  | "countdown"
  | "form"
  | "divider";

export interface Block {
  id: string;
  type: BlockType;
  content: Record<string, unknown>;
}

export interface ThemeSettings {
  primaryColor: string;
  secondaryColor: string;
  fontFamily: string;
  backgroundColor: string;
  textColor: string;
}

export const defaultTheme: ThemeSettings = {
  primaryColor: "#6366f1",
  secondaryColor: "#f59e0b",
  fontFamily: "Inter",
  backgroundColor: "#ffffff",
  textColor: "#111827",
};

export const blockDefaults: Record<BlockType, Record<string, unknown>> = {
  hero: {
    heading: "หัวข้อหลักของคุณ",
    subheading: "คำอธิบายสั้นๆ เพื่อดึงดูดความสนใจของลูกค้า",
    buttonText: "เริ่มต้นเลย",
    buttonUrl: "#",
    backgroundImage: "",
    align: "center",
  },
  features: {
    heading: "ฟีเจอร์เด่น",
    items: [
      { icon: "⚡", title: "รวดเร็ว", desc: "ประสิทธิภาพสูงสุด" },
      { icon: "🛡️", title: "ปลอดภัย", desc: "ข้อมูลของคุณปลอดภัย" },
      { icon: "💡", title: "ง่ายใช้", desc: "ใช้งานได้ทันที" },
    ],
  },
  text: {
    content: "เนื้อหาของคุณที่นี่ คลิกเพื่อแก้ไข",
    align: "left",
    size: "base",
  },
  image: {
    src: "",
    alt: "รูปภาพ",
    caption: "",
    width: "full",
  },
  cta: {
    heading: "พร้อมเริ่มต้นแล้วหรือยัง?",
    subheading: "ลงทะเบียนฟรีวันนี้ ไม่มีค่าใช้จ่ายแฝง",
    buttonText: "เริ่มต้นฟรี",
    buttonUrl: "#",
    bgColor: "#6366f1",
  },
  testimonial: {
    items: [
      {
        quote: "สินค้าดีมากเลยครับ ใช้แล้วประทับใจมาก",
        name: "สมชาย ใจดี",
        role: "ลูกค้าประจำ",
        avatar: "",
      },
    ],
  },
  video: {
    url: "https://www.youtube.com/embed/dQw4w9WgXcQ",
    title: "วิดีโอแนะนำ",
  },
  countdown: {
    heading: "โปรโมชั่นสิ้นสุดใน",
    targetDate: new Date(Date.now() + 7 * 24 * 60 * 60 * 1000).toISOString(),
    subtext: "อย่าพลาดโอกาสนี้!",
  },
  form: {
    heading: "ติดต่อเรา",
    fields: ["ชื่อ", "อีเมล", "เบอร์โทร"],
    buttonText: "ส่งข้อมูล",
    successMessage: "ขอบคุณ เราจะติดต่อกลับโดยเร็ว",
  },
  divider: {
    style: "solid",
    color: "#e5e7eb",
  },
};
