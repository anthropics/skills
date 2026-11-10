import { open, readFile, rename, unlink } from 'node:fs/promises'
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

// An existing file is overwritten in place, never replaced by a rename: the inode stays, and with it the owner, group,
// mode, ACLs, extended attributes and hard links. The new bytes go to a private temp file first, so if the overwrite
// fails part-way the full new workbook is still on disk and the error names it. A new file is written by rename.
export async function writeWorkbook(target, data) {
  const full = resolve(target)
  const temp = join(dirname(full), `.${basename(full)}.${process.pid}.tmp`)
  try {
    const t = await open(temp, 'wx', 0o600)
    try {
      await t.writeFile(data)
      await t.sync()
    } finally {
      await t.close()
    }
  } catch (e) {
    await unlink(temp).catch(() => {})
    throw new Failure(`could not write ${target}: ${e.message}`)
  }

  let handle
  try {
    handle = await open(full, 'r+')
  } catch (e) {
    if (e.code === 'ENOENT') {
      await rename(temp, full).catch(async (err) => {
        await unlink(temp).catch(() => {})
        throw new Failure(`could not write ${target}: ${err.message}`)
      })
      return
    }
    await unlink(temp).catch(() => {})
    throw new Failure(`could not write ${target}: ${e.message}; the original is unchanged`)
  }
  try {
    await handle.truncate(0)
    await handle.writeFile(data)
    await handle.sync()
  } catch (e) {
    await handle.close().catch(() => {})
    throw new Failure(`overwriting ${target} failed part-way (${e.message}); the complete new workbook is in ${temp}`, { recovery: temp })
  }
  await handle.close()
  await unlink(temp).catch(() => {})
}
