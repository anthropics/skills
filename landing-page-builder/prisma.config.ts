import { defineConfig } from "prisma/config";
import path from "node:path";

export default defineConfig({
  schema: "prisma/schema.prisma",
  migrations: {
    path: "prisma/migrations",
  },
  datasource: {
    url: `file:${path.join(process.cwd(), "prisma/dev.db")}`,
  },
});
