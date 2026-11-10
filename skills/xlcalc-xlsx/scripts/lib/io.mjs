import { chmod, readFile, rename, stat, unlink, writeFile } from 'node:fs/promises'
import { basename, dirname, extname, join, resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { Failure } from './engine.mjs'

// A spec or an ops file: JSON, or a module whose default export is the value or a function that returns it.
export async function readInput(path, ...args) {
  const full = resolve(path)
  const ext = extname(full).toLowerCase()
  if (ext === '.json') {
    try {
      return JSON.parse(await readFile(full, 'utf8'))
    } catch (e) {
      throw new Failure(`could not read ${path}: ${e.message}`)
    }
  }
  if (!['.mjs', '.js'].includes(ext)) throw new Failure(`${path}: expected .json, .mjs or .js`)
  const mod = await import(pathToFileURL(full).href)
  const value = mod.default
  if (value === undefined) throw new Failure(`${path} has no default export`)
  return typeof value === 'function' && args.length ? value(...args) : value
}

// Write through a temp file in the same directory, keeping the mode of the file it replaces
// (a 0600 workbook must not come out 0644 under the umask).
export async function writeAtomic(target, data) {
  const full = resolve(target)
  let mode
  try {
    mode = (await stat(full)).mode & 0o7777
  } catch {
    /* a new file */
  }
  const temp = join(dirname(full), `.${basename(full)}.${process.pid}.tmp`)
  try {
    await writeFile(temp, data, mode === undefined ? undefined : { mode })
    if (mode !== undefined) await chmod(temp, mode)
    await rename(temp, full)
  } catch (e) {
    await unlink(temp).catch(() => {})
    throw new Failure(`could not write ${target}: ${e.message}`)
  }
}
