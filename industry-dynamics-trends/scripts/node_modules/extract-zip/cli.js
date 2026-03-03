#!/usr/bin/env node

/* eslint-disable no-process-exit */

var extract = require('./')

var args = process.argv.slice(2)
var source = args[0]
var dest = args[1] || process.cwd()
if (!source) {
  console.error('Usage: extract-zip foo.zip <targetDirectory>')
  process.exit(1)
}

extract(source, { dir: dest })
  .catch(function (err) {
    console.error('error!', err)
    process.exit(1)
  })
