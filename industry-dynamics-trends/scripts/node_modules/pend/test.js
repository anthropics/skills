var assert = require('assert');
var Pend = require('./');

var tests = [
  {
    name: "basic",
    fn: testBasic,
  },
  {
    name: "max",
    fn: testWithMax,
  },
  {
    name: "callback twice",
    fn: testCallbackTwice,
  },
  {
    name: "calling wait twice",
    fn: testCallingWaitTwice,
  },
  {
    name: "hold()",
    fn: testHoldFn,
  },
];
var testCount = tests.length;

doOneTest();

function doOneTest() {
  var test = tests.shift();
  if (!test) {
    console.log(testCount + " tests passed.");
    return;
  }
  process.stdout.write(test.name + "...");
  test.fn(function() {
    process.stdout.write("OK\n");
    doOneTest();
  });
}

function testBasic(cb) {
  var pend = new Pend();
  var results = [];
  pend.go(function(cb) {
    results.push(1);
    setTimeout(function() {
      results.push(3);
      cb();
    }, 500);
  });
  pend.go(function(cb) {
    results.push(2);
    setTimeout(function() {
      results.push(4);
      cb();
    }, 1000);
  });
  pend.wait(function(err) {
    assert.deepEqual(results, [1,2,3,4]);
    cb();
  });
  assert.deepEqual(results, [1, 2]);
}

function testWithMax(cb) {
  var pend = new Pend();
  var results = [];
  pend.max = 2;
  pend.go(function(cb) {
    results.push('a');
    setTimeout(function() {
      results.push(1);
      cb();
    }, 500);
  });
  pend.go(function(cb) {
    results.push('b');
    setTimeout(function() {
      results.push(1);
      cb();
    }, 500);
  });
  pend.go(function(cb) {
    results.push('c');
    setTimeout(function() {
      results.push(2);
      cb();
    }, 100);
  });
  pend.wait(function(err) {
    assert.deepEqual(results, ['a', 'b', 1, 'c', 1, 2]);
    cb();
  });
  assert.deepEqual(results, ['a', 'b']);
}

function testCallbackTwice(cb) {
  var pend = new Pend();
  pend.go(function(cb) {
    setTimeout(cb, 100);
  });
  pend.go(function(cb) {
    cb();
    assert.throws(cb, /callback called twice/);
  });
  pend.wait(cb);
}

function testCallingWaitTwice(cb) {
  var pend = new Pend();
  pend.go(function(cb) {
    setTimeout(cb, 100);
  });
  pend.wait(function() {
    pend.go(function(cb) {
      setTimeout(cb, 50);
    });
    pend.go(function(cb) {
      setTimeout(cb, 10);
    });
    pend.go(function(cb) {
      setTimeout(cb, 20);
    });
    pend.wait(cb);
  });
}

function testHoldFn(cb) {
  var pend = new Pend();
  setTimeout(pend.hold(), 100);
  pend.go(function(cb) {
    cb();
  });
  pend.wait(cb);
}
