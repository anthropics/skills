# HoTT (Homotopy Type Theory) Patterns for Rocq/Coq

Guide for working with HoTT-specific features in Rocq (formerly Coq).

## HoTT Setup

### Required Flags

When compiling HoTT code:

```bash
python scripts/verify_proof.py file.v \
  --coq-flags "-R path/to/HoTT/theories HoTT -noinit -indices-matter"
```

### _CoqProject Configuration

```
-R path/to/HoTT/theories HoTT
-noinit
-indices-matter
```

## Key Differences from Standard Coq

1. **No Standard Library** - Use `-noinit` flag
2. **Universe Polymorphism** - Required (`-indices-matter`)
3. **Univalence Axiom** - Available
4. **Path Types** - Replace propositional equality

## Path Types

### Basic Path Construction

```coq
Require Import HoTT.

(* Path types replace = *)
Definition example_path {A : Type} (x y : A) (p : x = y) : x = y := p.

(* Path concatenation *)
Definition path_concat {A : Type} {x y z : A}
  (p : x = y) (q : y = z) : x = z := p @ q.

(* Path inversion *)
Definition path_inverse {A : Type} {x y : A}
  (p : x = y) : y = x := p^.
```

### Path Induction

```coq
(* Use path_ind instead of eq_ind *)
Definition path_induction_example {A : Type} (P : forall x y : A, x = y -> Type)
  (r : forall x, P x x idpath) {x y : A} (p : x = y) : P x y p :=
  match p with
  | idpath => r x
  end.
```

## Univalence

### Function Extensionality

```coq
Require Import HoTT.Basics.

(* Function extensionality is available *)
Theorem funext_example {A B : Type} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
  intro H.
  apply path_forall.
  exact H.
Qed.
```

### Univalence Axiom

```coq
(* Univalence: equivalence implies path equality of types *)
Check ua : forall A B, A <~> B -> A = B.
```

## Common HoTT Tactics

### Transport

```coq
(* Transport along paths *)
Definition transport_example {A : Type} (P : A -> Type)
  {x y : A} (p : x = y) : P x -> P y := transport P p.
```

### Apply Path

```coq
(* Apply function to path *)
Definition ap_example {A B : Type} (f : A -> B)
  {x y : A} (p : x = y) : f x = f y := ap f p.
```

## HoTT-Specific Lemmas

### Path Algebra

```coq
(* Paths form a groupoid *)
Lemma concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ idpath = p.

Lemma concat_1p {A : Type} {x y : A} (p : x = y) :
  idpath @ p = p.

Lemma concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = idpath.
```

## Practical HoTT Example

```coq
Require Import HoTT.

(* Prove that Bool has decidable equality *)
Definition bool_eq_dec : forall (b1 b2 : Bool), (b1 = b2) + (b1 <> b2).
Proof.
  intros [|] [|].
  - left. reflexivity.
  - right. intro p. exact (transport (fun b => if b then Unit else Empty) p tt).
  - right. intro p. exact (transport (fun b => if b then Empty else Unit) p tt).
  - left. reflexivity.
Defined.
```

## Resources

- HoTT Book: https://homotopytypetheory.org/book/
- Coq-HoTT library: https://github.com/HoTT/Coq-HoTT
- Use `SearchAbout` to find HoTT-specific lemmas
