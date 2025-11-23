# Rocq/Coq Standard Library Reference

## Commonly Used Modules

### Arith
```coq
Require Import Arith.
```
Provides: plus_n_O, plus_n_Sm, mult_n_O, etc.

### Lia
```coq
Require Import Lia.
```
Linear integer arithmetic solver (replaces Omega).

### List
```coq
Require Import List.
Import ListNotations.
```
Provides: app, length, rev, map, fold_left, fold_right

### Bool
```coq
Require Import Bool.
```
Provides: andb, orb, negb, if-then-else

### Nat
```coq
Require Import Nat.
```
Modern natural number library with many useful lemmas.

### Ring/Field
```coq
Require Import Ring.
Require Import Field.
```
Solvers for ring and field equations.

## Search Strategies

```coq
SearchAbout plus.        (* Find theorems mentioning plus *)
Search (?n + 0 = ?n).   (* Search for specific pattern *)
```
