var fdSlicer = require('../');
var fs = require('fs');
var crypto = require('crypto');
var path = require('path');
var streamEqual = require('stream-equal');
var assert = require('assert');
var Pend = require('pend');
var StreamSink = require('streamsink');

var describe = global.describe;
var it = global.it;
var before = global.before;
var beforeEach = global.beforeEach;
var after = global.after;

var testBlobFile = path.join(__dirname, "test-blob.bin");
var testBlobFileSize = 20 * 1024 * 1024;
var testOutBlobFile = path.join(__dirname, "test-blob-out.bin");

describe("FdSlicer", function() {
  before(function(done) {
    var out = fs.createWriteStream(testBlobFile);
    for (var i = 0; i < testBlobFileSize / 1024; i += 1) {
      out.write(crypto.pseudoRandomBytes(1024));
    }
    out.end();
    out.on('close', done);
  });
  beforeEach(function() {
    try {
      fs.unlinkSync(testOutBlobFile);
    } catch (err) {
    }
  });
  after(function() {
    try {
      fs.unlinkSync(testBlobFile);
      fs.unlinkSync(testOutBlobFile);
    } catch (err) {
    }
  });
  it("reads a 20MB file (autoClose on)", function(done) {
    fs.open(testBlobFile, 'r', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var actualStream = slicer.createReadStream();
      var expectedStream = fs.createReadStream(testBlobFile);

      var pend = new Pend();
      pend.go(function(cb) {
        slicer.on('close', cb);
      });
      pend.go(function(cb) {
        streamEqual(expectedStream, actualStream, function(err, equal) {
          if (err) return done(err);
          assert.ok(equal);
          cb();
        });
      });
      pend.wait(done);
    });
  });
  it("reads 4 chunks simultaneously", function(done) {
    fs.open(testBlobFile, 'r', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd);
      var actualPart1 = slicer.createReadStream({start: testBlobFileSize * 0/4, end: testBlobFileSize * 1/4});
      var actualPart2 = slicer.createReadStream({start: testBlobFileSize * 1/4, end: testBlobFileSize * 2/4});
      var actualPart3 = slicer.createReadStream({start: testBlobFileSize * 2/4, end: testBlobFileSize * 3/4});
      var actualPart4 = slicer.createReadStream({start: testBlobFileSize * 3/4, end: testBlobFileSize * 4/4});
      var expectedPart1 = slicer.createReadStream({start: testBlobFileSize * 0/4, end: testBlobFileSize * 1/4});
      var expectedPart2 = slicer.createReadStream({start: testBlobFileSize * 1/4, end: testBlobFileSize * 2/4});
      var expectedPart3 = slicer.createReadStream({start: testBlobFileSize * 2/4, end: testBlobFileSize * 3/4});
      var expectedPart4 = slicer.createReadStream({start: testBlobFileSize * 3/4, end: testBlobFileSize * 4/4});
      var pend = new Pend();
      pend.go(function(cb) {
        streamEqual(expectedPart1, actualPart1, function(err, equal) {
          assert.ok(equal);
          cb(err);
        });
      });
      pend.go(function(cb) {
        streamEqual(expectedPart2, actualPart2, function(err, equal) {
          assert.ok(equal);
          cb(err);
        });
      });
      pend.go(function(cb) {
        streamEqual(expectedPart3, actualPart3, function(err, equal) {
          assert.ok(equal);
          cb(err);
        });
      });
      pend.go(function(cb) {
        streamEqual(expectedPart4, actualPart4, function(err, equal) {
          assert.ok(equal);
          cb(err);
        });
      });
      pend.wait(function(err) {
        if (err) return done(err);
        fs.close(fd, done);
      });
    });
  });

  it("writes a 20MB file (autoClose on)", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var actualStream = slicer.createWriteStream();
      var inStream = fs.createReadStream(testBlobFile);

      slicer.on('close', function() {
        var expected = fs.createReadStream(testBlobFile);
        var actual = fs.createReadStream(testOutBlobFile);

        streamEqual(expected, actual, function(err, equal) {
          if (err) return done(err);
          assert.ok(equal);
          done();
        });
      });
      inStream.pipe(actualStream);
    });
  });

  it("writes 4 chunks simultaneously", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd);
      var actualPart1 = slicer.createWriteStream({start: testBlobFileSize * 0/4});
      var actualPart2 = slicer.createWriteStream({start: testBlobFileSize * 1/4});
      var actualPart3 = slicer.createWriteStream({start: testBlobFileSize * 2/4});
      var actualPart4 = slicer.createWriteStream({start: testBlobFileSize * 3/4});
      var in1 = fs.createReadStream(testBlobFile, {start: testBlobFileSize * 0/4, end: testBlobFileSize * 1/4});
      var in2 = fs.createReadStream(testBlobFile, {start: testBlobFileSize * 1/4, end: testBlobFileSize * 2/4});
      var in3 = fs.createReadStream(testBlobFile, {start: testBlobFileSize * 2/4, end: testBlobFileSize * 3/4});
      var in4 = fs.createReadStream(testBlobFile, {start: testBlobFileSize * 3/4, end: testBlobFileSize * 4/4});
      var pend = new Pend();
      pend.go(function(cb) {
        actualPart1.on('finish', cb);
      });
      pend.go(function(cb) {
        actualPart2.on('finish', cb);
      });
      pend.go(function(cb) {
        actualPart3.on('finish', cb);
      });
      pend.go(function(cb) {
        actualPart4.on('finish', cb);
      });
      in1.pipe(actualPart1);
      in2.pipe(actualPart2);
      in3.pipe(actualPart3);
      in4.pipe(actualPart4);
      pend.wait(function() {
        fs.close(fd, function(err) {
          if (err) return done(err);
          var expected = fs.createReadStream(testBlobFile);
          var actual = fs.createReadStream(testOutBlobFile);
          streamEqual(expected, actual, function(err, equal) {
            if (err) return done(err);
            assert.ok(equal);
            done();
          });
        });
      });
    });
  });

  it("throws on invalid ref", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      assert.throws(function() {
        slicer.unref();
      }, /invalid unref/);
      fs.close(fd, done);
    });
  });

  it("write stream emits error when max size exceeded", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var ws = slicer.createWriteStream({start: 0, end: 1000});
      ws.on('error', function(err) {
        assert.strictEqual(err.code, 'ETOOBIG');
        slicer.on('close', done);
      });
      ws.end(new Buffer(1001));
    });
  });

  it("write stream does not emit error when max size not exceeded", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var ws = slicer.createWriteStream({end: 1000});
      slicer.on('close', done);
      ws.end(new Buffer(1000));
    });
  });

  it("write stream start and end work together", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var ws = slicer.createWriteStream({start: 1, end: 1000});
      ws.on('error', function(err) {
        assert.strictEqual(err.code, 'ETOOBIG');
        slicer.on('close', done);
      });
      ws.end(new Buffer(1000));
    });
  });

  it("write stream emits progress events", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var ws = slicer.createWriteStream();
      var progressEventCount = 0;
      var prevBytesWritten = 0;
      ws.on('progress', function() {
        progressEventCount += 1;
        assert.ok(ws.bytesWritten > prevBytesWritten);
        prevBytesWritten = ws.bytesWritten;
      });
      slicer.on('close', function() {
        assert.ok(progressEventCount > 5);
        done();
      });
      for (var i = 0; i < 10; i += 1) {
        ws.write(new Buffer(16 * 1024 * 2));
      }
      ws.end();
    });
  });

  it("write stream unrefs when destroyed", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var ws = slicer.createWriteStream();
      slicer.on('close', done);
      ws.write(new Buffer(1000));
      ws.destroy();
    });
  });

  it("read stream unrefs when destroyed", function(done) {
    fs.open(testBlobFile, 'r', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd, {autoClose: true});
      var rs = slicer.createReadStream();
      rs.on('error', function(err) {
        assert.strictEqual(err.message, "stream destroyed");
        slicer.on('close', done);
      });
      rs.destroy();
    });
  });

  it("fdSlicer.read", function(done) {
    fs.open(testBlobFile, 'r', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd);
      var outBuf = new Buffer(1024);
      slicer.read(outBuf, 0, 10, 0, function(err, bytesRead, buf) {
        assert.strictEqual(bytesRead, 10);
        fs.close(fd, done);
      });
    });
  });

  it("fdSlicer.write", function(done) {
    fs.open(testOutBlobFile, 'w', function(err, fd) {
      if (err) return done(err);
      var slicer = fdSlicer.createFromFd(fd);
      slicer.write(new Buffer("blah\n"), 0, 5, 0, function() {
        if (err) return done(err);
        fs.close(fd, done);
      });
    });
  });
});

describe("BufferSlicer", function() {
  it("invalid ref", function() {
    var slicer = fdSlicer.createFromBuffer(new Buffer(16));
    slicer.ref();
    slicer.unref();
    assert.throws(function() {
      slicer.unref();
    }, /invalid unref/);
  });
  it("read and write", function(done) {
    var buf = new Buffer("through the tangled thread the needle finds its way");
    var slicer = fdSlicer.createFromBuffer(buf);
    var outBuf = new Buffer(1024);
    slicer.read(outBuf, 10, 11, 8, function(err) {
      if (err) return done(err);
      assert.strictEqual(outBuf.toString('utf8', 10, 21), "the tangled");
      slicer.write(new Buffer("derp"), 0, 4, 7, function(err) {
        if (err) return done(err);
        assert.strictEqual(buf.toString('utf8', 7, 19), "derp tangled");
        done();
      });
    });
  });
  it("createReadStream", function(done) {
    var str = "I never conquered rarely came, 16 just held such better days";
    var buf = new Buffer(str);
    var slicer = fdSlicer.createFromBuffer(buf);
    var inStream = slicer.createReadStream();
    var sink = new StreamSink();
    inStream.pipe(sink);
    sink.on('finish', function() {
      assert.strictEqual(sink.toString(), str);
      inStream.destroy();
      done();
    });
  });
  it("createWriteStream exceed buffer size", function(done) {
    var slicer = fdSlicer.createFromBuffer(new Buffer(4));
    var outStream = slicer.createWriteStream();
    outStream.on('error', function(err) {
      assert.strictEqual(err.code, 'ETOOBIG');
      done();
    });
    outStream.write("hi!\n");
    outStream.write("it warked\n");
    outStream.end();
  });
  it("createWriteStream ok", function(done) {
    var buf = new Buffer(1024);
    var slicer = fdSlicer.createFromBuffer(buf);
    var outStream = slicer.createWriteStream();
    outStream.on('finish', function() {
      assert.strictEqual(buf.toString('utf8', 0, "hi!\nit warked\n".length), "hi!\nit warked\n");
      outStream.destroy();
      done();
    });
    outStream.write("hi!\n");
    outStream.write("it warked\n");
    outStream.end();
  });
});
