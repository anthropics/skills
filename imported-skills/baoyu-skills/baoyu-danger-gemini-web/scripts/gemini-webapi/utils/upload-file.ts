import fs from 'node:fs';
import path from 'node:path';
import { readFile } from 'node:fs/promises';

import { Endpoint, Headers } from '../constants.js';

export async function upload_file(file: string, _proxy?: string | null): Promise<string> {
  if (!fs.existsSync(file) || !fs.statSync(file).isFile()) {
    throw new Error(`${file} is not a valid file.`);
  }

  const filename = path.basename(file);
  const content = await readFile(file);

  const form = new FormData();
  form.append('file', new Blob([content]), filename);

  const res = await fetch(Endpoint.UPLOAD, {
    method: 'POST',
    headers: { ...Headers.UPLOAD },
    body: form,
    redirect: 'follow',
  });

  if (!res.ok) {
    throw new Error(`Upload failed: ${res.status} ${res.statusText}`);
  }

  return await res.text();
}

export function parse_file_name(file: string): string {
  if (!fs.existsSync(file) || !fs.statSync(file).isFile()) {
    throw new Error(`${file} is not a valid file.`);
  }
  return path.basename(file);
}

export const uploadFile = upload_file;
export const parseFileName = parse_file_name;

