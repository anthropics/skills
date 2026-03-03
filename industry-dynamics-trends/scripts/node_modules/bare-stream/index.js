const stream = require('streamx')

const defaultEncoding = 'utf8'

module.exports = exports = stream.Stream

exports.pipeline = stream.pipeline

exports.isStream = stream.isStream
exports.isEnded = stream.isEnded
exports.isFinished = stream.isFinished
exports.isDisturbed = stream.isDisturbed

exports.getStreamError = stream.getStreamError

exports.Stream = exports

exports.Readable = class Readable extends stream.Readable {
  constructor(opts = {}) {
    super({
      ...opts,
      byteLength: null,
      byteLengthReadable: null,
      map: null,
      mapReadable: null
    })

    if (this._construct) this._open = this._construct

    if (this._read !== stream.Readable.prototype._read) {
      this._read = read.bind(this, this._read)
    }

    if (this._destroy !== stream.Stream.prototype._destroy) {
      this._destroy = destroy.bind(this, this._destroy)
    }
  }

  push(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    return super.push(chunk)
  }

  unshift(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    super.unshift(chunk)
  }
}

exports.Writable = class Writable extends stream.Writable {
  constructor(opts = {}) {
    super({
      ...opts,
      byteLength: null,
      byteLengthWritable,
      map: null,
      mapWritable: null
    })

    if (this._construct) this._open = this._construct

    if (this._write !== stream.Writable.prototype._write) {
      this._write = write.bind(this, this._write)
    }

    if (this._destroy !== stream.Stream.prototype._destroy) {
      this._destroy = destroy.bind(this, this._destroy)
    }
  }

  write(chunk, encoding, cb) {
    if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding)
    } else {
      encoding = 'buffer'
    }

    const result = super.write({ chunk, encoding })

    if (cb) stream.Writable.drained(this).then(() => cb(null), cb)

    return result
  }

  end(chunk, encoding, cb) {
    if (typeof chunk === 'function') {
      cb = chunk
      chunk = null
    } else if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    } else {
      encoding = 'buffer'
    }

    const result =
      chunk !== undefined && chunk !== null ? super.end({ chunk, encoding }) : super.end()

    if (cb) this.once('finish', () => cb(null))

    return result
  }
}

exports.Duplex = class Duplex extends stream.Duplex {
  constructor(opts = {}) {
    super({
      ...opts,
      byteLength: null,
      byteLengthReadable: null,
      byteLengthWritable,
      map: null,
      mapReadable: null,
      mapWritable: null
    })

    if (this._construct) this._open = this._construct

    if (this._read !== stream.Readable.prototype._read) {
      this._read = read.bind(this, this._read)
    }

    if (this._write !== stream.Duplex.prototype._write) {
      this._write = write.bind(this, this._write)
    }

    if (this._destroy !== stream.Stream.prototype._destroy) {
      this._destroy = destroy.bind(this, this._destroy)
    }
  }

  push(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    return super.push(chunk)
  }

  unshift(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    super.unshift(chunk)
  }

  write(chunk, encoding, cb) {
    if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding)
    } else {
      encoding = 'buffer'
    }

    const result = super.write({ chunk, encoding })

    if (cb) stream.Writable.drained(this).then(() => cb(null), cb)

    return result
  }

  end(chunk, encoding, cb) {
    if (typeof chunk === 'function') {
      cb = chunk
      chunk = null
    } else if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding)
    } else {
      encoding = 'buffer'
    }

    const result =
      chunk !== undefined && chunk !== null ? super.end({ chunk, encoding }) : super.end()

    if (cb) this.once('finish', () => cb(null))

    return result
  }
}

exports.Transform = class Transform extends stream.Transform {
  constructor(opts = {}) {
    super({
      ...opts,
      byteLength: null,
      byteLengthReadable: null,
      byteLengthWritable,
      map: null,
      mapReadable: null,
      mapWritable: null
    })

    if (this._transform !== stream.Transform.prototype._transform) {
      this._transform = transform.bind(this, this._transform)
    } else {
      this._transform = passthrough
    }
  }

  push(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    return super.push(chunk)
  }

  unshift(chunk, encoding) {
    if (typeof chunk === 'string') {
      chunk = Buffer.from(chunk, encoding || defaultEncoding)
    }

    super.unshift(chunk)
  }

  write(chunk, encoding, cb) {
    if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding)
    } else {
      encoding = 'buffer'
    }

    const result = super.write({ chunk, encoding })

    if (cb) stream.Writable.drained(this).then(() => cb(null), cb)

    return result
  }

  end(chunk, encoding, cb) {
    if (typeof chunk === 'function') {
      cb = chunk
      chunk = null
    } else if (typeof encoding === 'function') {
      cb = encoding
      encoding = null
    }

    if (typeof chunk === 'string') {
      encoding = encoding || defaultEncoding
      chunk = Buffer.from(chunk, encoding)
    } else {
      encoding = 'buffer'
    }

    const result =
      chunk !== undefined && chunk !== null ? super.end({ chunk, encoding }) : super.end()

    if (cb) this.once('finish', () => cb(null))

    return result
  }
}

exports.PassThrough = class PassThrough extends exports.Transform {}

exports.finished = function finished(stream, opts, cb) {
  if (typeof opts === 'function') {
    cb = opts
    opts = {}
  }

  if (!opts) opts = {}

  const { cleanup = false } = opts

  const done = () => {
    cb(exports.getStreamError(stream, { all: true }))

    if (cleanup) detach()
  }

  const detach = () => {
    stream.off('close', done)
    stream.off('error', noop)
  }

  if (stream.destroyed) {
    done()
  } else {
    stream.on('close', done)
    stream.on('error', noop)
  }

  return detach
}

function read(read, cb) {
  read.call(this, 65536)

  cb(null)
}

function write(write, data, cb) {
  write.call(this, data.chunk, data.encoding, cb)
}

function transform(transform, data, cb) {
  transform.call(this, data.chunk, data.encoding, cb)
}

function destroy(destroy, cb) {
  destroy.call(this, exports.getStreamError(this), cb)
}

function passthrough(data, cb) {
  cb(null, data.chunk)
}

function byteLengthWritable(data) {
  return data.chunk.byteLength
}

function noop() {}
