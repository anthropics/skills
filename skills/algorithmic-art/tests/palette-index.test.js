const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

// The template only defines helpers at top level, so p5 is not needed here.
const context = vm.createContext({});
const template = path.join(__dirname, '../templates/generator_template.js');
vm.runInContext(fs.readFileSync(template, 'utf8'), context);
vm.runInContext("params.colorPalette = ['red', 'green', 'blue']", context);

for (let index = -7; index <= 7; index++) {
    const actual = vm.runInContext('colorFromPalette(' + index + ')', context);
    const expected = ['red', 'green', 'blue'][((index % 3) + 3) % 3];
    assert.equal(actual, expected, 'palette index ' + index);
}
console.log('PASS: palette indices wrap in both directions');
