## v2.0.1 (Mar 29, 2021)

### IMPORTANT: Security Fix

> This version contains an important security fix. If you are using netmask `<=2.0.0`, please upgrade to `2.0.1` or above.

* Rewrite byte parsing without using JS `parseInt()`([commit](https://github.com/rs/node-netmask/commit/3f19a056c4eb808ea4a29f234274c67bc5a848f4))
  * This is [CVE-2021-29418](https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2021-29418).

### Bugfixes

* Add checks on spaces before and after bytes
  * This will now throw an exception when spaces are present like ' 1.2.3.4' or '1. 2.3.4' or '1.2.3.4 '.

### Internal Changes

* Avoid some useless memory allocations
* New Mocha testing suite, thanks @kaoudis [#36](https://github.com/rs/node-netmask/pull/36)

## v2.0.0 (Mar 19, 2021)

### Breaking Change

Previous API was treating IPs with less than for bytes as IP with a
netmask of the size of the provided bytes (1=8, 2=16, 3=24) and was
interpreting the IP as if it was completed with 0s on the right side.

*Proper IP parsing for these is to consider missing bytes as being 0s on
the left side.*

Mask size is no longer infered by the number of bytes provided.

This means that the input `216.240` will no longer be interpreted as `216.240.0.0/16`, but as `0.0.216.240/32`,
as per convention.

See [the change](https://github.com/rs/node-netmask/commit/9f9fc38c6db1a682d23289b5c9dc2009d957a00b).

### Bugfixes

* Fix improper parsing of hex bytes

## v1.1.0 (Mar 18, 2021)

### IMPORTANT: Security Fix

> This version contains an important security fix. If you are using netmask `<=1.0.6`, please upgrade to `1.1.0` or above.

* Fix improper parsing of octal bytes ([commit](https://github.com/rs/node-netmask/commit/4678fd840ad0b4730dbad2d415712c0782e886cc))
  * This is [CVE-2021-28918](https://sick.codes/sick-2021-011).
  * See also the [npm advisory](https://www.npmjs.com/advisories/1658)

### Other Changes

* Performance: Avoid large allocations when provided large netmasks (like `/8`)
  * Thanks @dschenkelman [#34](https://github.com/rs/node-netmask/pull/34)

## v1.0.6 (May 30, 2016)

* Changes before this release are not documented here. Please see [the commit list](https://github.com/rs/node-netmask/commits/master)
  or the [compare view](https://github.com/rs/node-netmask/compare/1.0.5...rs:1.0.6).
