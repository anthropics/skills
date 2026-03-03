/* It is important to test our Javascript output as well as our coffeescript, 
 * since code that is transpiled may be slightly different in effect from the
 * original.
 * 
 * Run these tests (against lib/netmask.js, not lib/netmask.coffee directly)
 * using mocha, after re-generating lib/netmask.js including your changes:
 *
 * mocha tests/netmask.js
 */

const assert = require('assert');
const Netmask = require('../').Netmask;

describe('Netmask', () => {
  describe('can build a block', () => {
    let block = new Netmask('10.1.2.0/24');

    it('should contain a sub-block', () => {
      let block1 = new Netmask('10.1.2.10/29');
      assert(block.contains(block1));
    });

    it('should contain another sub-block', () => {
      let block2 = new Netmask('10.1.2.10/31');
      assert(block.contains(block2));
    });

    it('should contain a third sub-block', () => {
      let block3 = new Netmask('10.1.2.20/32');
      assert(block.contains(block3));
    });
  });

  describe('when presented with an octet which is not a number', () => {
    let block = new Netmask('192.168.0.0/29')

    it('should throw', () => {
      assert.throws(() => block.contains('192.168.~.4'), Error);
    });
  });

  describe('can handle hexadecimal, octal, & decimal octets in input IP', () => {
    let block1 = new Netmask('31.0.0.0/19');
    let block2 = new Netmask('127.0.0.0/8');
    let block3 = new Netmask('255.0.0.1/12');
    let block4 = new Netmask('10.0.0.1/8');
    let block5 = new Netmask('1.0.0.1/4');

    describe('octal', () => {
      it('block 31.0.0.0/19 does not contain 031.0.5.5', () => {
        assert(!block1.contains('031.0.5.5'));
      }); 
      it('block 127.0.0.0/8 contains 0177.0.0.2 (127.0.0.2)', () => {
        assert(block2.contains('0177.0.0.2'));
      });
      it('block 255.0.0.1/12 does not contain 0255.0.0.2 (173.0.0.2)', () => {
        assert(!block3.contains('0255.0.0.2'));
      });
      it('block 10.0.0.1/8 contains 012.0.0.255 (10.0.0.255)', () => {
        assert(block4.contains('012.0.0.255'));
      });
      it('block 1.0.0.1/4 contains 01.02.03.04', () => {
        assert(block5.contains('01.02.03.04'));
      });
    });

    describe('hexadecimal', () => {
      it('block 31.0.0.0/19 does not contain 0x31.0.5.5', () => {
        assert(!block1.contains('0x31.0.5.5'));
      });
      it('block 127.0.0.0/8 contains 0x7f.0.0.0x2 (127.0.0.2)', () => {
        assert(block2.contains('0x7f.0.0.0x2'));
      });
      it('block 255.0.0.1/12 contains 0xff.0.0.2', () => {
        assert(block3.contains('0xff.0.0.2'));
      });
      it('block 10.0.0.1/8 does not contain 0x10.0.0.255', () => {
        assert(!block4.contains('0x10.0.0.255'));
      });
      it('block 1.0.0.1/4 contains 0x1.0x2.0x3.0x4', () => {
        assert(block5.contains('0x1.0x2.0x3.0x4'));
      });
    });

    describe('decimal', () => {
      it('block 31.0.0.0/19 contains 31.0.5.5', () => {
        assert(block1.contains('31.0.5.5'));
      });
      it('block 127.0.0.0/8 does not contain 128.0.0.2', () =>{
        assert(!block2.contains('128.0.0.2'));
      });
      it('block 255.0.0.1/12 contains 255.0.0.2', () => {
        assert(block3.contains('255.0.0.2'));
      });
      it('block 10.0.0.1/8 contains 10.0.0.255', () => {
        assert(block4.contains('10.0.0.255'));
      });
      it('block 1.0.0.1/4 contains 1.2.3.4', () => {
        assert(block5.contains('1.2.3.4'));
      });
    });
  });
});