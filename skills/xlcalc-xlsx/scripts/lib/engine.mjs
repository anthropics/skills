import { createRequire } from 'node:module'
import { join, resolve, dirname } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

export const MIN_VERSION = '0.85.0'
export const SCRIPTS_DIR = resolve(dirname(fileURLToPath(import.meta.url)), '..')

export class Failure extends Error {
  constructor(message, extra = {}, exitCode = 1) {
    super(message)
    this.extra = extra
    this.exitCode = exitCode
  }
}

function older(a, b) {
  const pa = a.split(/[.-]/).map(Number)
  const pb = b.split(/[.-]/).map(Number)
  for (let i = 0; i < 3; i++) if ((pa[i] || 0) !== (pb[i] || 0)) return (pa[i] || 0) < (pb[i] || 0)
  return false
}

// xlcalc is looked up, never installed: XLCALC_PATH, then this skill's scripts/, then the working directory.
export async function loadEngine() {
  const bases = [process.env.XLCALC_PATH, SCRIPTS_DIR, process.cwd()].filter(Boolean)
  const tooOld = []
  for (const base of bases) {
    const req = createRequire(join(resolve(base), 'noop.js'))
    let version
    try {
      version = req(req.resolve('xlcalc/package.json')).version
    } catch {
      continue
    }
    if (older(version, MIN_VERSION)) {
      tooOld.push(`${version} in ${base}`)
      continue
    }
    const load = (spec) => import(pathToFileURL(req.resolve(spec)).href)
    const [core, xlsx, keep, locales] = await Promise.all(
      ['xlcalc', 'xlcalc/xlsx', 'xlcalc/xlsx/keep', 'xlcalc/locales'].map(load),
    )
    return { version, core, xlsx, keep, locales }
  }
  throw new Failure(
    tooOld.length ? `xlcalc ${MIN_VERSION} or newer is needed; found ${tooOld.join(', ')}` : 'xlcalc is not installed',
    { hint: `npm install --prefix "${SCRIPTS_DIR}"` },
    3,
  )
}

export async function ensureLocale(engine, book) {
  if (book.locale && book.locale !== 'en-US') await engine.locales.loadLocale(book.locale)
}
