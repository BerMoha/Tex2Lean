import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Prelude — the vocabulary of Section 2

The setting is the opening line of Section 2 of the paper: *"Except when it is
clearly specified, in all this section `A` will be a ring with a unit `e`, `J` an
ideal of `A`, and `π : A → A/J` will be the canonical projection."*

So `A` is an associative ring with unit, **not** assumed commutative, **not**
assumed to be an algebra or a Banach algebra, and **not** assumed semi-prime —
the semi-primeness of Definition 1.2 is dropped by that opening line, and the
whole point of working in rings here is to cover `L(X)/F₀(X)`, which is not a
Banach algebra.

The ambient ring, the ideal and the projection are all taken from Mathlib and
nothing is redefined for them:

* `A` is `[Ring A]`;
* `J` is `(J : Ideal A) [J.IsTwoSided]`. The paper says only "ideal", but it
  forms `A/J` as a *ring* and uses `π` as a *ring* homomorphism
  (`π(a₁a₂) = π(a₁)π(a₂)` is the first line of the proof of claim (ii)), so `J`
  has to be two-sided. Mathlib's `Ideal A` is `Submodule A A`, i.e. the
  left-ideal notion, and `[J.IsTwoSided]` is exactly the missing half;
* `π` is `Ideal.Quotient.mk J : A →+* A ⧸ J`, whose kernel is `J` by
  `Ideal.Quotient.eq_zero_iff_mem`. That, and the fact that it is a ring hom,
  are the only properties of `J` the proposition uses. In particular `J = ⊥`
  and `J = ⊤` are both allowed; `J = ⊤` makes `A ⧸ J` the zero ring and the
  proposition degenerately true.

What is *not* in Mathlib, and so is introduced here, is Drazin invertibility:
a glob for a module whose name contains `Drazin` returns nothing, and the string
does not occur under `Mathlib/RingTheory`, `Mathlib/Analysis` or
`Mathlib/Algebra/Ring`.
-/

namespace Tex2lean.Model

/-! ## Vocabulary -/

/-- `IsDrazinInvOf x y k` says that `y` is a Drazin inverse of `x` of index at
most `k`, in the paper's own words (Section 2): `y * x * y = y`, `x * y = y * x`
and `x ^ k * y * x = x ^ k`.

Given `comm`, the third clause is the familiar `x ^ (k + 1) * y = x ^ k`, which
is the form the paper itself uses in the proof of Theorem 2.6.

`k` ranges over all of `ℕ`, as the paper's Section 2 writes it. The paper writes
`ℕ*` in Theorem 2.6; the two readings give the same predicate on `x`, because
`k = 0` reads `y * x = 1` (as `x ^ 0 = 1`) which with `comm` makes `x` a unit,
and a unit already satisfies the `k = 1` clause. Fixing `k : ℕ` here settles the
question once. -/
structure IsDrazinInvOf {R : Type*} [Ring R] (x y : R) (k : ℕ) : Prop where
  /-- `y` is an inner inverse for itself along `x`. -/
  bab : y * x * y = y
  /-- `x` and `y` commute. -/
  comm : x * y = y * x
  /-- `y` inverts `x` on the `k`-th power. -/
  pow : x ^ k * y * x = x ^ k

/-- `x` is **Drazin invertible** in the unital ring `R`: there are `y : R` and
`k : ℕ` with `y` a Drazin inverse of `x` of index at most `k`.

The witness `y` is in fact unique (Drazin 1958) and is *the* Drazin inverse
`xᴰ`, and the least admissible `k` is the index of `x`. Neither uniqueness nor
the index is needed for Proposition 2.4, which asks only for existence, so this
is a bare existential and uniqueness is deferred. -/
def IsDrazinInvertible {R : Type*} [Ring R] (x : R) : Prop :=
  ∃ (y : R) (k : ℕ), IsDrazinInvOf x y k

/-! ## The quantity -/

/-- `a` is a **B-Fredholm element of `A` modulo `J`**: `π a` is Drazin
invertible in `A ⧸ J` (Definition 1.2 of the paper, transplanted to a unital
ring by the opening line of Section 2).

This is the single property Proposition 2.4 is about. It is a property of the
pair `(a, J)` and it depends on `a` only through `π a` — which is literally
claim (iii).

Mathlib defines no such predicate (it has no Drazin API at all, see the module
docstring), so there is nothing here to cross-check against and no theorem in
this file. The honest sanity checks — units, nilpotents and idempotents are
Drazin invertible — are content, not surface, and belong under `Analysis/`. -/
def IsBFredholm {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] (a : A) : Prop :=
  IsDrazinInvertible (Ideal.Quotient.mk J a)

end Tex2lean.Model
