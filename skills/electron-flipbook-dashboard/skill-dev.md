---
name: electron-flipbook-dashboard-dev
description: Flipbook Dashboard 개발자 레퍼런스. 아키텍처, IPC 패턴, 핵심 설계 결정, 빌드 설정, DB 스키마, 트러블슈팅. 기능 추가 또는 유지보수 시 참고.
version: "2.1.0"
target: 개발자 / 유지보수 담당자
project: C:\dev\flipbook-dashboard
---

# Flipbook Dashboard — 개발자 레퍼런스

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

---

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
└── db/database.ts (마이그레이션)      │   ├── adminStore.ts (UI용)
                                    │   └── settingsStore.ts
                                    ├── lib/pdfUtils.ts
                                    └── electron.d.ts  ← window.api 타입
```

---

## DB 스키마

```sql
-- v1
CREATE TABLE books (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  title TEXT NOT NULL,
  file_path TEXT NOT NULL,       -- {hash}.pdf  (userData/library/)
  cover_path TEXT,               -- {id}.png    (userData/covers/)
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

-- v2
CREATE TABLE presets (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  name TEXT UNIQUE NOT NULL,
  data TEXT NOT NULL,       -- JSON: { settings: {}, bookOrder: number[] }
  created_at DATETIME DEFAULT CURRENT_TIMESTAMP
);
```

### userData 폴더 구조
```
%APPDATA%\Flipbook Dashboard\      (설치형)
FlipbookData\                      (포터블, EXE 옆에 생성)
├── library/        ← PDF 파일 ({hash}.pdf)
├── covers/         ← 표지 썸네일 ({id}.png)
├── backgrounds/    ← 배경 이미지 ({uuid}.ext)
├── characters/     ← 캐릭터 이미지 ({uuid}.ext)
└── flipbook.db     ← SQLite DB
```
> `ensureUserDataDirs()` 가 앱 시작 시 자동 생성. `doImportFromPath` 내에서도 방어적으로 재생성.

---

## 핵심 설계 결정

### 1. safe-asset:// 프로토콜 (보안 파일 서빙)

`file://` 대신 커스텀 프로토콜 사용. CSP 호환 + 경로 traversal 방어.

```typescript
// main.ts — app.whenReady() 이전에 반드시 등록
protocol.registerSchemesAsPrivileged([{
  scheme: 'safe-asset',
  privileges: { secure: true, standard: true, supportFetchAPI: true, stream: true }
}])

protocol.handle('safe-asset', async (request) => {
  const url = new URL(request.url)
  const type = url.hostname   // 'pdf' | 'cover' | 'background' | 'character'
  const folder = { pdf: 'library', cover: 'covers', background: 'backgrounds', character: 'characters' }[type]
  const baseDir = path.join(app.getPath('userData'), folder)
  const safeName = path.basename(decodeURIComponent(url.pathname.slice(1)))
  const filePath = path.resolve(baseDir, safeName)
  if (!filePath.startsWith(baseDir)) return new Response('Forbidden', { status: 403 })
  return net.fetch(pathToFileURL(filePath).toString())
})
```

### 2. CSP (index.html — 자주 빠뜨림)

```html
<meta http-equiv="Content-Security-Policy"
  content="default-src 'self' safe-asset:;
           script-src 'self' blob:;
           style-src 'self' 'unsafe-inline';
           img-src 'self' data: safe-asset: blob:;
           worker-src 'self' blob:;
           connect-src 'self' safe-asset:;" />
```
> ⚠️ `connect-src`에 `safe-asset:` 누락 시 PDF.js 내부 fetch 차단 → PDF 읽기 불가

### 3. PDF.js 워커 경로

```typescript
// pdfUtils.ts — ?url import는 프로덕션에서 경로 깨짐
pdfjsLib.GlobalWorkerOptions.workerSrc = new URL(
  'pdfjs-dist/build/pdf.worker.min.mjs',
  import.meta.url
).toString()
```

### 4. 스트리밍 SHA-256 해시 (중복 감지)

```typescript
function hashFile(filePath: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const hash = crypto.createHash('sha256')
    const stream = fs.createReadStream(filePath, { highWaterMark: 64 * 1024 })
    stream.on('data', (chunk) => hash.update(chunk))
    stream.on('end', () => resolve(hash.digest('hex')))
    stream.on('error', reject)
  })
}
// PDF 저장 경로: userData/library/{hash}.pdf
```

### 5. FlipbookViewer — stale closure 방지

```typescript
useEffect(() => {
  let destroyed = false
  let loadedDoc: PDFDocumentProxy | null = null   // 로컬 변수 필수

  loadPdf(`safe-asset://pdf/${book.file_path}`).then((d) => {
    if (destroyed) { d.destroy(); return }
    loadedDoc = d
    setDoc(d)
  })

  return () => {
    destroyed = true
    loadedDoc?.destroy()   // state.doc 아닌 로컬 변수 사용 — stale closure 방지
  }
}, [book.file_path])
```

### 6. 관리자 세션 (Main Process에서만)

```typescript
// session.ts — Renderer Zustand 우회 불가
const adminSessions = new Map<number, number>()  // senderId → expiry timestamp

// 대부분의 쓰기 IPC 핸들러 첫 줄
if (!isAdminSession(event.sender.id)) return { success: false, error: 'Unauthorized' }

// 예외: dashboard:importFromPath — 인증 없이 허용 (뷰어 배포용)
// Renderer adminStore는 UI 토글용만 — 실제 권한 체크 아님
```

### 7. 포터블 EXE userData 경로

```typescript
// main.ts — app.whenReady() 이전
if (process.env.PORTABLE_EXECUTABLE_DIR) {
  app.setPath('userData', path.join(process.env.PORTABLE_EXECUTABLE_DIR, 'FlipbookData'))
}
```

### 8. webContents 소멸 버그

```typescript
// ❌ 'closed' 이벤트 시점엔 webContents 이미 소멸
win.on('closed', () => revokeAdminSession(win.webContents.id))

// ✅ 창 생성 직후 id 캡처
const wcId = win.webContents.id
win.on('closed', () => revokeAdminSession(wcId))
```

### 9. 싱글 인스턴스 + .flipbook 더블클릭

```typescript
// main.ts
let pendingImportPath: string | null = null

const gotTheLock = app.requestSingleInstanceLock()
if (!gotTheLock) {
  app.quit()
} else {
  app.on('second-instance', (_event, commandLine) => {
    const filePath = extractFlipbookPath(commandLine)
    if (filePath) {
      pendingImportPath = filePath
      mainWindow?.webContents.send('dashboard:pendingFile', filePath)
    }
    mainWindow?.focus()
  })
}

app.whenReady().then(() => {
  pendingImportPath = extractFlipbookPath(process.argv)
  ipcMain.handle('dashboard:getPendingFile', () => {
    const p = pendingImportPath
    pendingImportPath = null  // 소비 후 초기화 (1회만)
    return p
  })
})
```

### 10. adm-zip 외부화 필수

```typescript
// electron.vite.config.ts
main: {
  build: {
    rollupOptions: {
      external: ['better-sqlite3', 'bcryptjs', 'adm-zip'],  // 누락 시 빌드 에러
    }
  }
}
```

### 11. 뷰어 배포 흐름 — .flipbook 자동 가져오기 위치

> ⚠️ **반드시 `Dashboard.tsx`에서 처리** — `AdminPanel.tsx`에 두면 안 됨

**이유**: `AdminPanel`은 어드민 로그인 후에야 마운트됨 → 비인증 뷰어는 절대 실행되지 않음.

```typescript
// ✅ src/pages/Dashboard.tsx — 항상 마운트, 인증 불필요
useEffect(() => {
  async function checkPendingFile(filePath: string) {
    const result = await window.api.dashboard.importFromPath(filePath)
    await refresh()  // 성공/실패 무관하게 항상 호출 (부분 성공 대응)
    if (result.success) {
      if (result.settings) settings.update(result.settings as any)
      // 화면 하단 toast 메시지 표시
    }
  }
  window.api.dashboard.getPendingFile().then((fp) => { if (fp) checkPendingFile(fp) })
  const unsub = window.api.dashboard.onPendingFile(checkPendingFile)
  return unsub
}, [])

// ❌ src/components/admin/AdminPanel.tsx — 어드민만 마운트됨, 사용 금지
```

### 12. import 후 책 목록 갱신 — refresh() 필수

```typescript
// bookStore.ts
refresh: async () => {
  const books = await window.api.books.list()  // DB에서 다시 읽음
  set({ books })
}

// ⚠️ import 후 refresh() 를 안 부르면 책이 DB에 있어도 화면에 안 나옴
// Dashboard.tsx: await refresh() — 항상 호출 (성공/실패 무관)
// AdminPanel.tsx: await refresh() — applyImportResult 첫 줄에서 호출
```

---

## .flipbook 패키지 구조

```
flipbook-2025-01-15.flipbook  (ZIP 포맷, adm-zip으로 생성)
├── manifest.json
│   {
│     "version": 2,
│     "exportedAt": "ISO string",
│     "appVersion": "1.0.0",
│     "settings": { key: value, ... },
│     "books": [{ hash, title, page_count, file_size, order_index }],
│     "adminPasswordHash": "$2a$12$...",   // bcrypt (원본 불가 복원)
│     "adminRecoveryHash": "$2a$12$..."
│   }
├── pdfs/
│   └── {sha256hash}.pdf
├── backgrounds/
│   └── {uuid}.jpg             (background_type === 'image' 일 때만)
└── characters/
    └── {uuid}.png             (character_id 있을 때만)
```

### 비밀번호 해시 전송 방식
```
내보내기: safeStorage.decryptString(저장된값) → bcrypt 해시 → manifest에 포함
가져오기: manifest의 bcrypt 해시 → safeStorage.encryptString() → DB 저장
```
> bcrypt 해시는 기기 독립적이므로 다른 PC에서도 같은 비밀번호로 로그인 가능.
> 원본 비밀번호는 절대 전송되지 않음.

### 가져오기 보안: 화이트리스트
```typescript
const ALLOWED_KEYS = new Set([
  'background_type', 'background_value', 'background_id',
  'main_topic', 'sub_topic', 'character_id', 'character_ext',
  'grid_columns', 'admin_session_timeout'
])
// admin-password-hash 등 민감 키는 일반 설정으로 가져오기 불가
// 비밀번호 해시는 별도 saveRawHash() 경로로만 처리
```

### PDF 가져오기 — 견고한 처리
```typescript
// 각 PDF를 독립적으로 처리 — 하나 실패해도 나머지 계속
for (const bookMeta of manifest.books) {
  try {
    const libDir = ud('library')
    if (!fs.existsSync(libDir)) fs.mkdirSync(libDir, { recursive: true })  // 방어적 생성
    fs.writeFileSync(path.join(libDir, pdfFilename), pdfData)
    db.prepare('INSERT INTO books ...').run(...)
    importedCount++
  } catch {
    continue  // 개별 실패 → 다음 책 계속
  }
}
```

---

## IPC 전체 목록

### books
| 채널 | 인증 | 설명 |
|------|------|------|
| `books:list` | ❌ | 전체 책 목록 |
| `books:add` | ✅ | PDF 단건 추가 (해시 검증 포함) |
| `books:addBatch` | ✅ | 여러 PDF 일괄 추가 + `books:addProgress` 이벤트 |
| `books:updateCover` | ✅ | 표지 PNG 업데이트 |
| `books:updatePageCount` | ✅ | 페이지 수 업데이트 |
| `books:delete` | ✅ | 삭제 + 파일 정리 |
| `books:reorder` | ✅ | 순서 변경 |
| `books:rename` | ✅ | 제목 변경 |
| `dialog:openPdf` | ❌ | 파일 선택 다이얼로그 |

### auth
| 채널 | 인증 | 설명 |
|------|------|------|
| `auth:hasPassword` | ❌ | 비밀번호 설정 여부 |
| `auth:setPassword` | ❌ | 초기 설정 (복구 코드 반환) |
| `auth:verify` | ❌ | 비밀번호 검증 + 세션 생성 |
| `auth:verifyRecovery` | ❌ | 복구 코드 검증 |
| `auth:logout` | ❌ | 세션 해제 |
| `auth:isAdmin` | ❌ | 현재 세션 유효 여부 |

### presets & dashboard
| 채널 | 인증 | 설명 |
|------|------|------|
| `presets:list` | ❌ | 프리셋 목록 |
| `presets:save` | ✅ | 현재 상태 스냅샷 저장 |
| `presets:load` | ✅ | 프리셋 복원 |
| `presets:delete` | ✅ | 프리셋 삭제 |
| `dashboard:export` | ✅ | .flipbook ZIP 내보내기 (다이얼로그) |
| `dashboard:import` | ✅ | .flipbook ZIP 가져오기 (다이얼로그) |
| `dashboard:importFromPath` | ❌ | .flipbook ZIP 가져오기 (경로 직접) — **뷰어도 사용 가능** |
| `dashboard:getPendingFile` | ❌ | argv에서 감지한 .flipbook 경로 반환 (1회) |

### 이벤트 (Main → Renderer)
| 채널 | 설명 |
|------|------|
| `books:addProgress` | addBatch 진행률 `{ file, current, total }` |
| `dashboard:pendingFile` | 앱 실행 중 .flipbook 더블클릭 시 경로 전달 |

---

## 플립북 페이지 레이아웃

```
표지 단독(1) → [짝수=왼쪽 | 홀수=오른쪽] → ... → [마지막+빈페이지(홀수 시)]
```

```typescript
// FlipbookViewer.tsx
const bodyCount = Math.max(0, pageCount - 1)
const needsPadding = bodyCount % 2 !== 0
const totalSlots = pageCount + (needsPadding ? 1 : 0)

<HTMLFlipBook showCover={true} size="fixed" usePortrait={false} ...>
```

---

## 빌드 설정

```bash
npm run dev               # 개발 서버 + Electron
npm run build             # NSIS + 포터블 동시
npm run build:installer   # NSIS만 (.flipbook 파일 연결 등록)
npm run build:portable    # 포터블만
```

### package.json 핵심 설정
```json
{
  "scripts": {
    "prebuild": "node scripts/patch-builder.js"
  },
  "build": {
    "fileAssociations": [{
      "ext": "flipbook",
      "name": "Flipbook Dashboard Package",
      "icon": "build-resources/icon.ico",
      "role": "Editor"
    }],
    "asarUnpack": ["**/node_modules/better-sqlite3/**/*", "**/*.node"]
  }
}
```

### 결과물
```
release/
├── Flipbook Dashboard Setup 1.0.0.exe   (101.8 MB) ← 배포용
└── FlipbookDashboard-Portable-1.0.0.exe (101.9 MB)
```

---

## 보안

| 항목 | 구현 |
|------|------|
| 비밀번호 | bcryptjs (salt 12) + Electron safeStorage (OS 키체인 암호화) |
| 복구 코드 | `randomBytes(8)` → `XXXX-XXXX-XXXX-XXXX`, bcrypt 해시 저장 |
| 브루트포스 | 5회 실패 → 15분 잠금 (Main Process) |
| 파일 경로 | `path.basename()` + `startsWith(baseDir)` 이중 검증 |
| DevTools | 프로덕션에서 F12 / Ctrl+Shift+I 차단 |
| 설정 가져오기 | ALLOWED_KEYS 화이트리스트 (민감 키 차단) |
| IPC 인증 | 쓰기 핸들러에 `isAdminSession()` 체크 (importFromPath 예외) |
| 비밀번호 전송 | bcrypt 해시만 전송, 수신측 safeStorage로 재암호화 |

---

## 자주 발생하는 문제

### 가져오기 후 책이 안 보임

```
원인 A: AdminPanel 수동 가져오기 — refresh() 미호출
해결: AdminPanel.applyImportResult 에서 await refresh() 를 첫 줄에 호출

원인 B: doImportFromPath가 PDF 쓰기 중 오류 → success:false 반환
       → Dashboard.tsx 에서 success 체크 후 refresh() 미호출
해결: Dashboard checkPendingFile에서 result.success 관계없이 await refresh() 항상 호출

원인 C: PDF 루프 중 예외 → 일부 책만 DB 등록
해결: PDF 루프를 개별 try-catch로 감싸 partial success 허용
```

### `Cannot find module 'adm-zip'`
```
원인: 프로젝트 외부 폴더에서 npm install 실행
해결: C:\dev\flipbook-dashboard 에서 npm install adm-zip
     electron.vite.config.ts external 배열에 'adm-zip' 포함 확인
```

### `Object has been destroyed`
```
원인: 'closed' 이벤트 콜백에서 win.webContents.id 접근
해결: const wcId = win.webContents.id 를 창 생성 직후 캡처
```

### PDF 읽기 안 됨
```
확인 1: index.html CSP의 connect-src에 safe-asset: 있는지
확인 2: pdfUtils.ts 워커 경로가 import.meta.url 방식인지 (?url import 금지)
확인 3: FlipbookViewer cleanup의 stale closure
```

### 빌드 시 winCodeSign exit code 2
```
원인: Windows Developer Mode 없음 → macOS 심볼릭 링크 생성 실패 (무시해도 됨)
해결: scripts/patch-builder.js 가 prebuild 훅으로 자동 패치
     패치 실패 시 node_modules/builder-util/out/util.js 수동 패치:
     exitCode === 2 → reject 대신 resolve(undefined)
```

### better-sqlite3 네이티브 모듈 오류
```bash
npm install --ignore-scripts
npx @electron/rebuild -f -w better-sqlite3
```

### 표지 중복 생성
```
원인: BookGrid에 generatingRef(Set) 없음
해결: useRef<Set<number>>(new Set()) 로 진행 중인 book.id 추적
```

### 비밀번호 설정 화면 안 뜸 (첫 실행)
```
원인: PasswordModal이 항상 'verify' step으로 시작
해결: useEffect → auth.hasPassword() → false면 step = 'setup'
```

---

## 파일 구조 (핵심만)

```
flipbook-dashboard/
├── electron/
│   ├── main.ts              # 프로토콜, 싱글 인스턴스, 포터블 경로, 창 생성
│   ├── preload.ts           # contextBridge window.api 노출
│   ├── ipc/
│   │   ├── books.ts         # CRUD + 스트리밍 해시 + addBatch + 진행 이벤트
│   │   ├── auth.ts          # bcrypt + safeStorage + 브루트포스 방어
│   │   ├── assets.ts        # 배경/캐릭터 파일 저장/삭제
│   │   ├── settings.ts      # app_settings CRUD
│   │   ├── presets.ts       # 프리셋 CRUD + .flipbook ZIP 내보내기/가져오기
│   │   └── session.ts       # 관리자 세션 Map + 브루트포스 카운터
│   └── db/database.ts       # WAL + 마이그레이션 + ensureUserDataDirs()
├── src/
│   ├── pages/Dashboard.tsx  # .flipbook 더블클릭 감지 + import + refresh (인증 무관)
│   ├── components/
│   │   ├── viewer/FlipbookViewer.tsx      # PDF 렌더링 + 책장 애니메이션
│   │   ├── dashboard/BookGrid.tsx         # 썸네일 자동 생성 + 드래그&드롭 + 초기 refresh
│   │   ├── dashboard/BookCard.tsx         # NEW 뱃지 (7일 이내)
│   │   ├── dashboard/UploadProgress.tsx   # addBatch 진행률
│   │   ├── header/DashboardHeader.tsx
│   │   ├── admin/AdminPanel.tsx           # 수동 내보내기/가져오기(어드민) + refresh() 포함
│   │   └── admin/PasswordModal.tsx        # 초기 설정 / 로그인 / 복구
│   ├── store/
│   │   ├── bookStore.ts       # 책 목록 + CRUD 액션 + refresh()
│   │   ├── adminStore.ts      # UI 토글용 (실제 권한은 Main에서)
│   │   └── settingsStore.ts   # initialSettings hydration + update()
│   ├── lib/pdfUtils.ts        # loadPdf() + generateThumbnail()
│   ├── electron.d.ts          # window.api 전체 타입
│   └── types.ts               # Book 등 공통 타입
├── index.html                 # CSP (safe-asset: 필수)
├── electron.vite.config.ts    # 3-target, adm-zip external
├── scripts/
│   ├── patch-builder.js       # winCodeSign exit code 2 패치
│   └── generate-icon.js       # 순수 Node.js ICO 생성 (zlib)
└── build-resources/icon.ico   # 앱 + .flipbook 파일 아이콘
```
