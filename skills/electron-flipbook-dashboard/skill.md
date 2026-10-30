---
name: electron-flipbook-dashboard
description: Electron 기반 PDF 플립북 대시보드 앱 구축 스킬. PDF를 업로드하면 표지 썸네일 그리드로 보여주고, 클릭하면 책장 넘기는 애니메이션으로 읽을 수 있는 데스크탑 앱. 관리자 모드(비밀번호 보호), 배경·캐릭터 커스터마이징, 프리셋 저장/불러오기, .flipbook 패키지 원클릭 배포(더블클릭 자동 가져오기, 인증 불필요), NSIS 인스톨러 + 포터블 EXE 포함.
version: "2.1.0"
project: C:\dev\flipbook-dashboard
---

# Electron Flipbook Dashboard

PDF를 업로드하고 책장 넘기는 애니메이션으로 읽는 오프라인 데스크탑 앱.
관리자/뷰어 두 가지 모드로 운영되며 `.flipbook` 패키지 파일로 원클릭 배포 가능.
**뷰어는 비밀번호 없이 바로 책 목록을 볼 수 있음.**

## 기술 스택

| 레이어 | 기술 | 이유 |
|--------|------|------|
| 프레임워크 | Electron 30 + electron-vite | 데스크탑 + 빠른 빌드 |
| UI | React 18 + TypeScript + Tailwind CSS | 타입 안전 + 유틸리티 CSS |
| PDF 뷰어 | react-pageflip + pdfjs-dist | 책장 넘김 애니메이션 |
| DB | better-sqlite3 (WAL 모드) | 오프라인 로컬 DB |
| 인증 | bcryptjs + Electron safeStorage | 순수 JS (네이티브 빌드 불필요) |
| 상태관리 | Zustand (3개 스토어 분리) | 최소한의 보일러플레이트 |
| ZIP 패키징 | adm-zip | .flipbook 패키지 생성/추출 |

## 아키텍처

```
Main Process (Node.js)           Renderer Process (React)
─────────────────────            ─────────────────────────
electron/
├── main.ts          ←─ IPC ──→  src/
│   ├── safe-asset:// 프로토콜       ├── pages/Dashboard.tsx  ← .flipbook 감지 담당
│   ├── 싱글 인스턴스 잠금            ├── components/
│   └── 포터블 userData 경로         │   ├── viewer/FlipbookViewer.tsx
├── ipc/                              │   ├── dashboard/BookGrid.tsx
│   ├── books.ts (CRUD + 해시)        │   ├── dashboard/BookCard.tsx
│   ├── auth.ts (bcrypt + 세션)       │   ├── header/DashboardHeader.tsx
│   ├── assets.ts (배경/캐릭터)       │   ├── admin/AdminPanel.tsx
│   ├── settings.ts                   │   └── admin/PasswordModal.tsx
│   ├── presets.ts (프리셋 + ZIP)    ├── store/
│   └── session.ts (브루트포스 방어)   │   ├── bookStore.ts
└── db/database.ts (마이그레이션)      │   ├── adminStore.ts
                                    │   └── settingsStore.ts
                                    ├── lib/pdfUtils.ts
                                    └── electron.d.ts
```

## 핵심 설계 결정

### 1. safe-asset:// 커스텀 프로토콜
PDF, 표지, 배경, 캐릭터 파일을 `file://` 대신 커스텀 프로토콜로 서빙.
- 경로 traversal 공격 방어
- CSP와 호환 (connect-src, img-src에 `safe-asset:` 추가 필요)
- PDF.js의 내부 fetch도 이 프로토콜 사용

```typescript
// main.ts — app.whenReady() 이전에 반드시 등록
protocol.registerSchemesAsPrivileged([{
  scheme: 'safe-asset',
  privileges: { secure: true, standard: true, supportFetchAPI: true, stream: true }
}])

protocol.handle('safe-asset', async (request) => {
  const url = new URL(request.url)
  const type = url.hostname   // 'pdf' | 'cover' | 'background' | 'character'
  const filename = decodeURIComponent(url.pathname.slice(1))
  const folder = { pdf: 'library', cover: 'covers', background: 'backgrounds', character: 'characters' }[type]
  const baseDir = path.join(app.getPath('userData'), folder)
  const safeName = path.basename(filename)
  const filePath = path.resolve(baseDir, safeName)
  if (!filePath.startsWith(baseDir)) return new Response('Forbidden', { status: 403 })
  return net.fetch(pathToFileURL(filePath).toString())
})
```

### 2. CSP 설정 (index.html — 가장 자주 빠뜨리는 곳)
```html
<meta http-equiv="Content-Security-Policy"
  content="default-src 'self' safe-asset:;
           script-src 'self' blob:;
           style-src 'self' 'unsafe-inline';
           img-src 'self' data: safe-asset: blob:;
           worker-src 'self' blob:;
           connect-src 'self' safe-asset:;" />
```
> **connect-src에 safe-asset: 누락 시 PDF.js 내부 fetch가 차단되어 PDF 읽기 불가**

### 3. PDF.js 워커 경로
```typescript
// pdfUtils.ts — ?url import는 프로덕션에서 경로 깨짐. import.meta.url 사용
pdfjsLib.GlobalWorkerOptions.workerSrc = new URL(
  'pdfjs-dist/build/pdf.worker.min.mjs',
  import.meta.url
).toString()
```

### 4. 스트리밍 SHA-256 해시 (중복 PDF 감지)
```typescript
// 전체 파일을 메모리에 올리지 않음 (대용량 PDF 대응)
function hashFile(filePath: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const hash = crypto.createHash('sha256')
    const stream = fs.createReadStream(filePath, { highWaterMark: 64 * 1024 })
    stream.on('data', (chunk) => hash.update(chunk))
    stream.on('end', () => resolve(hash.digest('hex')))
    stream.on('error', reject)
  })
}
```

### 5. FlipbookViewer — stale closure 방지
```typescript
useEffect(() => {
  let destroyed = false
  let loadedDoc: PDFDocumentProxy | null = null   // 로컬 변수로 참조

  loadPdf(`safe-asset://pdf/${book.file_path}`)
    .then((d) => {
      if (destroyed) { d.destroy(); return }
      loadedDoc = d
      setDoc(d)
    })

  return () => {
    destroyed = true
    loadedDoc?.destroy()   // state의 doc이 아닌 로컬 변수 사용
  }
}, [book.file_path])
```

### 6. 관리자 세션 — Main Process에서만 관리
```typescript
// session.ts (Main Process)
const adminSessions = new Map<number, number>()  // senderId → expiry timestamp

// Renderer의 Zustand adminStore는 UI 표시용만
// 실제 권한 체크는 항상 isAdminSession(event.sender.id)로
// 단, dashboard:importFromPath는 예외 (뷰어도 사용 가능)
```

### 7. 포터블 EXE userData 경로
```typescript
// main.ts — app.whenReady() 이전
if (process.env.PORTABLE_EXECUTABLE_DIR) {
  app.setPath('userData', path.join(process.env.PORTABLE_EXECUTABLE_DIR, 'FlipbookData'))
}
```

### 8. webContents 소멸 버그 방지
```typescript
// main.ts — 'closed' 이벤트 시점에 webContents는 이미 소멸됨
// BAD:  win.on('closed', () => revokeAdminSession(win.webContents.id))
// GOOD: id를 미리 캡처
const wcId = win.webContents.id
win.on('closed', () => revokeAdminSession(wcId))
```

### 9. 싱글 인스턴스 잠금 + .flipbook 더블클릭 처리
앱이 이미 실행 중일 때 .flipbook 파일을 더블클릭하면 새 창 대신 기존 창에 파일 경로 전달.

```typescript
// main.ts
let mainWindow: BrowserWindow | null = null
let pendingImportPath: string | null = null

function extractFlipbookPath(argv: string[]): string | null {
  for (const arg of argv.slice(1)) {
    if (arg.endsWith('.flipbook') && fs.existsSync(arg)) return arg
  }
  return null
}

const gotTheLock = app.requestSingleInstanceLock()
if (!gotTheLock) {
  app.quit()  // 이미 실행 중이면 종료
} else {
  app.on('second-instance', (_event, commandLine) => {
    const filePath = extractFlipbookPath(commandLine)
    if (filePath) {
      pendingImportPath = filePath
      mainWindow?.webContents.send('dashboard:pendingFile', filePath)
    }
    if (mainWindow?.isMinimized()) mainWindow.restore()
    mainWindow?.focus()
  })
}

// 앱 시작 시 argv에서 .flipbook 감지 (첫 실행 시 더블클릭)
app.whenReady().then(() => {
  pendingImportPath = extractFlipbookPath(process.argv)
  ipcMain.handle('dashboard:getPendingFile', () => {
    const p = pendingImportPath
    pendingImportPath = null  // 한 번만 소비
    return p
  })
  // ...
})
```

### 10. adm-zip 외부화 설정
```typescript
// electron.vite.config.ts
main: {
  build: {
    rollupOptions: {
      external: ['better-sqlite3', 'bcryptjs', 'adm-zip'],  // adm-zip 반드시 포함
    }
  }
}
```

## .flipbook 패키지 시스템 (원클릭 배포)

### 패키지 구조
```
flipbook-2025-01-15.flipbook  (ZIP 포맷)
├── manifest.json             ← 설정 + 책 메타데이터 + 비밀번호 해시
├── pdfs/
│   ├── {hash1}.pdf           ← 실제 PDF 파일 전부
│   └── {hash2}.pdf
├── backgrounds/
│   └── {uuid}.jpg            ← 배경 이미지 (있으면)
└── characters/
    └── {uuid}.png            ← 캐릭터 이미지 (있으면)
```

### manifest.json 구조
```json
{
  "version": 2,
  "exportedAt": "2025-01-15T09:00:00.000Z",
  "appVersion": "1.0.0",
  "settings": { "background_type": "color", "main_topic": "...", ... },
  "books": [{ "hash": "sha256...", "title": "책 제목", "page_count": 120, "file_size": 5000000, "order_index": 0 }],
  "adminPasswordHash": "$2a$12$...",   // bcrypt 해시 (원본 비밀번호 아님)
  "adminRecoveryHash": "$2a$12$..."    // bcrypt 해시
}
```
> 비밀번호 해시는 bcrypt이므로 원본 비밀번호 복원 불가. 받는 쪽에서 safeStorage로 재암호화.

### 내보내기 핵심 코드
```typescript
// electron/ipc/presets.ts — dashboard:export (어드민 전용)
ipcMain.handle('dashboard:export', async (event) => {
  if (!isAdminSession(event.sender.id)) return { success: false, error: 'Unauthorized' }

  const zip = new AdmZip()

  // manifest.json (설정 + 책 목록 + 비밀번호 해시)
  const adminPasswordHash = loadRawHash('admin-password-hash')  // safeStorage 복호화
  const manifest = { version: 2, settings: settingsMap, books: [...], adminPasswordHash }
  zip.addFile('manifest.json', Buffer.from(JSON.stringify(manifest, null, 2), 'utf-8'))

  // PDF 파일들
  for (const book of books) {
    const pdfPath = path.join(ud('library'), `${book.file_hash}.pdf`)
    if (fs.existsSync(pdfPath)) zip.addLocalFile(pdfPath, 'pdfs')
  }

  zip.writeZip(saveResult.filePath)
})
```

### 가져오기 핵심 코드
```typescript
// electron/ipc/presets.ts — doImportFromPath (인증 불필요)
async function doImportFromPath(filePath: string) {
  const zip = new AdmZip(filePath)
  const manifest = JSON.parse(zip.readAsText(zip.getEntry('manifest.json')!))

  // ① 설정 복원 (화이트리스트 키만)
  const ALLOWED_KEYS = new Set(['background_type', 'background_value', ...])
  settingsTx()  // SQLite 트랜잭션

  // ② 이미지 복원 (배경, 캐릭터)

  // ③ 비밀번호 해시 복원 (bcrypt → 이 기기의 safeStorage로 재암호화)
  if (manifest.adminPasswordHash) saveRawHash('admin-password-hash', manifest.adminPasswordHash)

  // ④ PDF 복원 — 각 책 독립 처리 (하나 실패해도 나머지 계속)
  for (const bookMeta of manifest.books) {
    try {
      if (!pdfEntry) continue
      if (existing) continue  // 중복 스킵

      const libDir = ud('library')
      if (!fs.existsSync(libDir)) fs.mkdirSync(libDir, { recursive: true })  // 방어적 생성
      fs.writeFileSync(path.join(libDir, pdfFilename), pdfData)
      db.prepare('INSERT INTO books ...').run(...)
      importedCount++
    } catch {
      continue  // 개별 PDF 실패 — 다음 책 계속
    }
  }

  return { success: true, settings: allSettings, bookCount: importedCount, totalBooks: manifest.books.length }
}
```

### Dashboard.tsx에서 더블클릭 자동 가져오기 처리
> ⚠️ **AdminPanel이 아닌 Dashboard에서 처리** — 뷰어(비인증 상태)도 동작하도록

```typescript
// src/pages/Dashboard.tsx — 항상 마운트됨 (인증 불필요)
useEffect(() => {
  async function checkPendingFile(filePath: string) {
    const result = await window.api.dashboard.importFromPath(filePath)
    await refresh()  // 성공/실패 관계없이 항상 refresh (부분 성공 대응)
    if (result.success) {
      if (result.settings) settings.update(result.settings as any)
      // 완료 메시지 표시 (4초 후 사라짐)
    }
  }

  // 앱 시작 시 대기 중인 파일 확인 (첫 실행 더블클릭)
  window.api.dashboard.getPendingFile().then((filePath) => {
    if (filePath) checkPendingFile(filePath)
  })

  // 앱 실행 중 새 .flipbook 파일 더블클릭 시 실시간 이벤트
  const unsub = window.api.dashboard.onPendingFile((filePath) => {
    checkPendingFile(filePath)
  })
  return unsub
}, [])
```

### AdminPanel에서 수동 가져오기 (어드민 전용)
```typescript
// src/components/admin/AdminPanel.tsx
const { refresh } = useBookStore()  // 책 목록 갱신용

async function applyImportResult(result) {
  await refresh()  // 반드시 호출 — 미호출 시 책이 DB에 있어도 화면에 안 나옴
  if (result.success && result.settings) {
    settings.update(result.settings as any)
    flashMsg(`✅ 가져오기 완료 (책 ${imported}권 추가)`)
  }
}
```
> ⚠️ **`refresh()` 미호출이 "책 안 보임" 버그의 원인** — import 후 반드시 호출 필요

### 파일 연결 등록 (package.json)
```json
"fileAssociations": [
  {
    "ext": "flipbook",
    "name": "Flipbook Dashboard Package",
    "description": "Flipbook Dashboard 패키지 파일",
    "icon": "build-resources/icon.ico",
    "role": "Editor"
  }
]
```
> NSIS 인스톨러 설치 시 자동 등록. 포터블은 수동으로 "연결 프로그램" 설정 필요.

## 뷰어 배포 흐름 (비밀번호 없이 바로 보기)

```
보내는 쪽 (어드민):
  어드민 로그인 → 📦 내보내기 → flipbook-날짜.flipbook 생성

받는 쪽 (뷰어):
  1. Setup.exe 설치
  2. .flipbook 더블클릭
  3. 앱 자동 실행 → 책 목록 즉시 표시 ✅ (비밀번호 불필요)
```

**설계 원칙:**
- `dashboard:importFromPath` IPC는 인증 체크 없음 (뷰어도 호출 가능)
- 파일 감지 로직은 `Dashboard.tsx`에 위치 (항상 마운트, 인증 상태 무관)
- `AdminPanel.tsx`는 감지 로직 없음 (어드민 로그인 후에야 마운트되므로 부적합)

## 프리셋 시스템

현재 대시보드 상태(설정 + 책 순서)를 이름 붙여 저장하고 불러오는 기능.

```sql
CREATE TABLE IF NOT EXISTS presets (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  name TEXT UNIQUE NOT NULL,
  data TEXT NOT NULL,       -- JSON: { settings, bookOrder: number[] }
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

## 표지 썸네일 생성 (자동)

```typescript
// BookGrid.tsx
const generatingRef = useRef<Set<number>>(new Set())  // 중복 방지

useEffect(() => {
  for (const book of books) {
    if (!book.cover_path && !generatingRef.current.has(book.id)) {
      generateBookCover(book)
    }
  }
}, [books])
```

## NEW 뱃지

7일 이내 추가된 책에 자동 표시.

```typescript
// BookCard.tsx
const isNew = book.created_at
  ? (Date.now() - new Date(book.created_at).getTime()) < 7 * 24 * 60 * 60 * 1000
  : false
```

## DB 스키마

```sql
CREATE TABLE books (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  title TEXT NOT NULL,
  file_path TEXT NOT NULL,       -- {hash}.pdf (library/ 하위)
  cover_path TEXT,               -- {id}.png (covers/ 하위)
  page_count INTEGER DEFAULT 0,
  file_size INTEGER DEFAULT 0,
  file_hash TEXT UNIQUE,         -- SHA-256 (중복 방지)
  order_index INTEGER DEFAULT 0,
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE app_settings (key TEXT PRIMARY KEY, value TEXT);
-- 주요 키: background_type, background_value, background_id,
--          main_topic, sub_topic, character_id, character_ext,
--          grid_columns, admin_session_timeout,
--          admin-password-hash, admin-recovery-hash (safeStorage 암호화)

CREATE TABLE presets (          -- v2 마이그레이션
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  name TEXT UNIQUE NOT NULL,
  data TEXT NOT NULL,
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

## 보안

| 항목 | 구현 |
|------|------|
| 비밀번호 | bcryptjs (salt rounds 12) + Electron safeStorage (OS 키체인) |
| 복구 코드 | randomBytes(8) → XXXX-XXXX-XXXX-XXXX 형식, bcrypt 해시 저장 |
| 브루트포스 | 5회 실패 → 15분 잠금 (Main Process session.ts) |
| 파일 경로 | path.basename() + startsWith(baseDir) 이중 검증 |
| DevTools | 프로덕션에서 F12 / Ctrl+Shift+I 차단 |
| 관리자 세션 | Main Process Map으로 관리 (Renderer Zustand 우회 불가) |
| 설정 가져오기 | ALLOWED_KEYS 화이트리스트로 허용된 키만 적용 |
| 비밀번호 전송 | bcrypt 해시만 전송 (원본 불가 복원), safeStorage 재암호화 |

## 빌드 및 배포

### 개발 실행
```bash
npm run dev
```

### 프로덕션 빌드
```bash
npm run build             # NSIS 인스톨러 + 포터블 동시 빌드
npm run build:installer   # NSIS 인스톨러만 → .flipbook 파일 연결 자동 등록
npm run build:portable    # 포터블 EXE만
```

### 빌드 결과물 위치
```
release/
├── Flipbook Dashboard Setup 1.0.0.exe   ← 배포용 (설치형, 파일 연결 등록)
└── FlipbookDashboard-Portable-1.0.0.exe ← 포터블 (설치 없이 실행)
```

### 배포 패키지 전달 방법
```
USB or 공유폴더에 2개 파일만 전달:
├── Flipbook Dashboard Setup 1.0.0.exe   ← 1. 먼저 설치
└── flipbook-날짜.flipbook               ← 2. 더블클릭 → 책 목록 즉시 표시
```

## 자주 발생하는 문제

### 가져오기 후 책이 안 보임
```
원인 A: AdminPanel 수동 가져오기 후 refresh() 미호출
해결: AdminPanel.applyImportResult에서 await refresh() 호출 필수

원인 B: doImportFromPath가 success:false 반환 (PDF 쓰기 실패 등)
해결: 성공/실패 관계없이 Dashboard에서 refresh() 항상 호출
     doImportFromPath 내 PDF 루프를 개별 try-catch로 감쌈
```

### PDF 읽기 안 됨
1. `index.html` CSP의 `connect-src`에 `safe-asset:` 누락 확인
2. `pdfUtils.ts` 워커 경로가 `?url` import인지 확인 → `import.meta.url` 방식으로 교체
3. FlipbookViewer cleanup에서 stale closure 확인

### adm-zip 모듈 못 찾음
```
Error: Cannot find module 'adm-zip'
```
- `npm install adm-zip`을 **프로젝트 폴더**에서 실행했는지 확인
- `electron.vite.config.ts`의 `external` 배열에 `'adm-zip'` 포함 확인

### Object has been destroyed
```
TypeError: Object has been destroyed at BrowserWindow.<anonymous>
```
`win.webContents.id`를 'closed' 이벤트 콜백 안에서 접근하면 발생.
webContents id를 창 생성 직후 변수에 저장해서 사용.

### better-sqlite3 빌드 오류
```bash
npm install --ignore-scripts
npx @electron/rebuild -f -w better-sqlite3
```

### 빌드 시 winCodeSign exit code 2
```
원인: Windows Developer Mode 없음 → macOS 심볼릭 링크 생성 실패 (무시해도 됨)
해결: scripts/patch-builder.js가 prebuild 훅으로 자동 패치
```

## 파일 구조 (핵심만)

```
flipbook-dashboard/
├── electron/
│   ├── main.ts              # 프로토콜, 싱글 인스턴스, 포터블 경로, 창 생성
│   ├── preload.ts           # contextBridge window.api 노출
│   ├── ipc/
│   │   ├── books.ts         # 책 CRUD + 스트리밍 해시 + addBatch
│   │   ├── auth.ts          # bcrypt + safeStorage + 브루트포스
│   │   ├── assets.ts        # 배경/캐릭터 파일 저장
│   │   ├── settings.ts      # app_settings CRUD
│   │   ├── presets.ts       # 프리셋 CRUD + .flipbook 내보내기/가져오기
│   │   └── session.ts       # 관리자 세션 Map
│   └── db/database.ts       # SQLite WAL + 마이그레이션 (v1: books, v2: presets)
├── src/
│   ├── pages/Dashboard.tsx  # 루트 페이지, .flipbook 더블클릭 감지, 가져오기 처리
│   ├── components/
│   │   ├── viewer/FlipbookViewer.tsx
│   │   ├── dashboard/BookGrid.tsx    # 썸네일 자동 생성, NEW 뱃지, 초기 refresh
│   │   ├── dashboard/BookCard.tsx    # NEW 뱃지, 7일 이내 감지
│   │   ├── dashboard/UploadProgress.tsx
│   │   ├── header/DashboardHeader.tsx
│   │   ├── admin/AdminPanel.tsx      # 프리셋 UI, 수동 내보내기/가져오기 (어드민 전용)
│   │   └── admin/PasswordModal.tsx
│   ├── store/
│   │   ├── bookStore.ts     # refresh() — import 후 반드시 호출
│   │   ├── adminStore.ts    # UI용만 (실제 권한은 Main에서)
│   │   └── settingsStore.ts # initialSettings hydration + update()
│   ├── lib/pdfUtils.ts      # loadPdf + generateThumbnail
│   ├── electron.d.ts        # window.api 전체 타입 정의
│   └── types.ts
├── index.html               # CSP 설정 (safe-asset: 필수)
├── electron.vite.config.ts  # 3-target 빌드, adm-zip external
├── scripts/
│   ├── patch-builder.js     # winCodeSign 심볼릭 링크 패치
│   └── generate-icon.js     # 순수 Node.js ICO 생성
└── build-resources/icon.ico # 앱 아이콘 (.flipbook 파일 아이콘으로도 사용)
```
