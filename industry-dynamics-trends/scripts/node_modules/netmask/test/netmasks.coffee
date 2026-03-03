vows = require 'vows'
assert = require 'assert'
util = require 'util'
Netmask = require('../lib/netmask').Netmask

fixtures =
[
    # addr                          mask                base                newmask             bitmask
    ['209.157.68.22/255.255.224.0', null,               '209.157.64.0',     '255.255.224.0',    19]
    ['209.157.68.22',               '255.255.224.0',    '209.157.64.0',     '255.255.224.0',    19]
    ['209.157.70.33/19',            null,               '209.157.64.0',     '255.255.224.0',    19]
    ['209.157.70.33',               null,               '209.157.70.33',    '255.255.255.255',  32]
    ['140.174.82',                  null,               '140.174.0.82',     '255.255.255.255',  32]
    ['140.174',                     null,               '140.0.0.174',      '255.255.255.255',  32]
    ['10',                          null,               '0.0.0.10',         '255.255.255.255',  32]
    ['10/8',                        null,               '0.0.0.0',          '255.0.0.0',        8]
    ['209.157.64/19',               null,               '209.157.0.0',      '255.255.224.0',    19]
    ['216.140.48.16/32',            null,               '216.140.48.16',    '255.255.255.255',  32]
    ['209.157/17',                  null,               '209.0.0.0',        '255.255.128.0',    17]
    ['0.0.0.0/0',                   null,               '0.0.0.0',          '0.0.0.0',          0]
    ['0xffffffff',                  null,               '255.255.255.255',  '255.255.255.255',  32]
    ['1.1',                         null,               '1.0.0.1',          '255.255.255.255',  32]
    ['1.0xffffff',                  null,               '1.255.255.255',    '255.255.255.255',  32]
    ['1.2.3',                       null,               '1.2.0.3',          '255.255.255.255',  32]
    ['1.2.0xffff',                  null,               '1.2.255.255',      '255.255.255.255',  32]
]

contexts = []

fixtures.forEach (fixture) ->
    [addr, mask, base, newmask, bitmask] = fixture
    context = topic: -> new Netmask(addr, mask)
    context["base is `#{base}'"] = (block) -> assert.equal block.base, base
    context["mask is `#{newmask}'"] = (block) -> assert.equal block.mask, newmask
    context["bitmask is `#{bitmask}'"] = (block) -> assert.equal block.bitmask, bitmask
    context["toString is `#{base}/`#{bitmask}'"] = (block) -> assert.equal block.toString(), block.base + "/" + block.bitmask
    contexts["for #{addr}" + (if mask then " with #{mask}" else '')] = context

vows.describe('Netmaks parsing').addBatch(contexts).export(module)

vows.describe('Netmask contains IP')
    .addBatch
        'block 192.168.1.0/24':
            topic: -> new Netmask('192.168.1.0/24')
            'contains IP 192.168.1.0': (block) -> assert.ok block.contains('192.168.1.0')
            'contains IP 192.168.1.255': (block) -> assert.ok block.contains('192.168.1.255')
            'contains IP 192.168.1.63': (block) -> assert.ok block.contains('192.168.1.63')
            'does not contain IP 192.168.0.255': (block) -> assert.ok not block.contains('192.168.0.255')
            'does not contain IP 192.168.2.0': (block) -> assert.ok not block.contains('192.168.2.0')
            'does not contain IP 10.168.2.0': (block) -> assert.ok not block.contains('10.168.2.0')
            'does not contain IP 209.168.2.0': (block) -> assert.ok not block.contains('209.168.2.0')
            'contains block 192.168.1.0/24': (block) -> assert.ok block.contains('192.168.1.0/24')
            'contains block 192.168.1 (0.192.168.10)': (block) -> assert.ok not block.contains('192.168.1')
            'does not contains block 192.168.1.128/25': (block) -> assert.ok block.contains('192.168.1.128/25')
            'does not contain block 192.168.1.0/23': (block) -> assert.ok not block.contains('192.168.1.0/23')
            'does not contain block 192.168.2.0/24': (block) -> assert.ok not block.contains('192.168.2.0/24')
            'toString equals 192.168.1.0/24': (block) -> assert.equal block.toString(), '192.168.1.0/24'
        'block 192.168.0.0/24':
            topic: -> new Netmask('192.168.0.0/24')
            'does not contain block 192.168 (0.0.192.168)': (block) -> assert.ok not block.contains('192.168')
            'does not contain block 192.168.0.0/16': (block) -> assert.ok not block.contains('192.168.0.0/16')
        'block 31.0.0.0/8':
            topic: -> new Netmask('31.0.0.0/8')
            'contains IP 31.5.5.5': (block) -> assert.ok block.contains('31.5.5.5')
            'does not contain IP 031.5.5.5 (25.5.5.5)': (block) -> assert.ok not block.contains('031.5.5.5')
            'does not contain IP 0x31.5.5.5 (49.5.5.5)': (block) -> assert.ok not block.contains('0x31.5.5.5')
            'does not contain IP 0X31.5.5.5 (49.5.5.5)': (block) -> assert.ok not block.contains('0X31.5.5.5')
        'block 127.0.0.0/8':
            topic: -> new Netmask('127.0.0.0/8')
            'contains IP 127.0.0.2': (block) -> assert.ok block.contains('127.0.0.2')
            'contains IP 0177.0.0.2 (127.0.0.2)': (block) -> assert.ok block.contains('0177.0.0.2')
            'contains IP 0x7f.0.0.2 (127.0.0.2)': (block) -> assert.ok block.contains('0x7f.0.0.2')
            'does not contains IP 127 (0.0.0.127)': (block) -> assert.ok not block.contains('127')
            'does not contains IP 0177 (0.0.0.127)': (block) -> assert.ok not block.contains('0177')
        'block 0.0.0.0/24':
            topic: -> new Netmask('0.0.0.0/0')
            'contains IP 0.0.0.0': (block) -> assert.ok block.contains('0.0.0.0')
            'contains IP 0': (block) -> assert.ok block.contains('0')
            'contains IP 10 (0.0.0.10)': (block) -> assert.ok block.contains('10')
            'contains IP 010 (0.0.0.8)': (block) -> assert.ok block.contains('010')
            'contains IP 0x10 (0.0.0.16)': (block) -> assert.ok block.contains('0x10')

    .export(module)

vows.describe('Netmask forEach')
    .addBatch
        'block 192.168.1.0/24':
            topic: -> new Netmask('192.168.1.0/24')
            'should loop through all ip addresses': (block) ->
                called = 0
                block.forEach (ip, long, index) ->
                    called = index
                assert.equal (called + 1), 254
        'block 192.168.1.0/23':
            topic: -> new Netmask('192.168.1.0/23')
            'should loop through all ip addresses': (block) ->
                called = 0
                block.forEach (ip, long, index) ->
                    called = index
                assert.equal (called + 1), 510
    .export(module)