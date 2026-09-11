# File plan — Tex2lean

> A working document, written as this pass finished. The blueprint at the end of the run supersedes it.

| Path | Role | Purpose |
| --- | --- | --- |
| `Tex2lean/Model/Prelude.lean` | audit-surface | The vocabulary, and the quantity the theorem is about |
| `Tex2lean/Model/Pseudocode.lean` | audit-surface | The algorithm, transcribed from the paper |
| `Tex2lean/Model/Theorem.lean` | audit-surface | The one theorem this development is for |

## Skeletons

### `Tex2lean/Model/Prelude.lean`

Imports: `Mathlib.RingTheory.Ideal.Quotient.Defs`

```lean
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

```

### `Tex2lean/Model/Pseudocode.lean`

Imports: `Tex2lean.Model.Prelude`, `Tex2lean.Meta.ModelClosure`

```lean
import Tex2lean.Model.Prelude
import Tex2lean.Meta.ModelClosure

/-!
# Pseudocode — there is no algorithm, and nothing here is probabilistic

The paper is pure algebra. It contains no algorithm, no computation, no sampling
and no probability: Proposition 2.4 is an ordinary `Prop` over a ring, not a
statement about a distribution, and there is no `PMF` anywhere in this
development. Writing one would be inventing a sample space the paper does not
have. The only thing in the paper that resembles a construction is the
extraction of a Drazin-inverse witness `(y, k)` from a hypothesis and the
assembly of a new one for the conclusion — in claim (ii) the paper's route
produces `y = π(a₁)ᴰ * π(a₂)ᴰ` — and that is witness-building inside a proof,
not a procedure the theorem is about.

So what this file carries is the other half of its job: **the object the
theorem's claims are about**, named once so a referee can see it.

Proposition 2.4 is a closure statement about a single set,

  `BF(A, J) = π⁻¹ {x ∈ A ⧸ J | x is Drazin invertible}`,

and its three claims say that this set is closed under, respectively, addition
of two members that annihilate each other modulo `J`, multiplication of two
members that commute modulo `J`, and perturbation by an element of `J`. No
numerical quantity enters — no index, no dimension, no norm. (The index
`i(a) = τ([a, a₀])` of Definition 3.2 belongs to Section 3 and plays no role in
Section 2.)
-/

namespace Tex2lean.Model

/-- `bFredholm J` is the set of B-Fredholm elements of `A` modulo `J`, i.e. the
preimage under `π : A →+* A ⧸ J` of the Drazin invertible elements of `A ⧸ J`.

This is `BF(A, J)`, the set whose closure properties are the three claims of
Proposition 2.4. -/
def bFredholm {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] : Set A :=
  {a : A | IsBFredholm J a}

#modelClosure bFredholm

end Tex2lean.Model

```

### `Tex2lean/Model/Theorem.lean`

Imports: `Tex2lean.Model.Prior`, `Tex2lean.Model.Pseudocode`, `Tex2lean.Meta.ModelClosure`

```lean
import Tex2lean.Model.Prior
import Tex2lean.Model.Pseudocode
import Tex2lean.Meta.ModelClosure

/-!
# The headline result — Proposition 2.4

*Let `a₁` and `a₂` be elements of `A` which are B-Fredholm elements in `A`
modulo `J`. Then:*

* *(i) if `a₁ a₂ ∈ J` and `a₂ a₁ ∈ J`, then `a₁ + a₂` is a B-Fredholm element in
  `A` modulo `J`;*
* *(ii) if `a₁ a₂ - a₂ a₁ ∈ J`, then `a₁ a₂` is a B-Fredholm element in `A`
  modulo `J`;*
* *(iii) for each `j ∈ J`, `a₁ + j` is a B-Fredholm element in `A` modulo `J`.*

Unwinding `IsBFredholm`, the three claims are exactly: (i) if `π a₁ * π a₂ = 0`
and `π a₂ * π a₁ = 0` then `π (a₁ + a₂)` is Drazin invertible; (ii) if `π a₁`
and `π a₂` commute then `π (a₁ * a₂) = π a₁ * π a₂` is Drazin invertible;
(iii) `π (a₁ + j) = π a₁`, which is Drazin invertible by hypothesis.

Nothing can fail here: all three claims are deterministic algebraic
implications, and none of them is a probabilistic statement.

Every hypothesis the paper states is present and none is added. In particular
there is no norm, no completeness, no scalar field, no semi-primeness, no
primitivity and no socle: the opening line of Section 2 replaces Definition
1.2's semi-prime Banach algebra by a bare unital ring, and importing any of
those would weaken the theorem for no reason. `J` is an arbitrary two-sided
ideal — neither proper nor non-zero is assumed.

Two shape notes for the referee.

* The paper's preamble assumes both `a₁` and `a₂` are B-Fredholm, but claim
  (iii) mentions only `a₁` and `j`; `h₂` is genuinely unused by (iii). The
  statement below is faithful to the printed text and carries it anyway. A
  standalone (iii) over a single B-Fredholm element is an immediate consequence
  and belongs under `Analysis/`, not on this surface.
* The proof of (i) in the paper concludes "So `a₁ + a₂` is a B-Fredholm element
  in `A`", dropping "modulo `J`". B-Fredholmness is only ever defined relative
  to an ideal, so `J` is carried explicitly in every claim.

The two results the paper's proof borrows — Drazin's additivity corollary
[DR, Corollary 1] for (i), and the commuting-product lemma [P10, Prop. 2.6],
which the paper transfers from unital algebras to rings with the words
"similarly to", for (ii) — are neither in Mathlib nor proved in the paper. They
are the real work of this development. They are *not* assumed here: `Prior` is
still empty, so as it stands this theorem borrows nothing.
-/

namespace Tex2lean.Model

/-- **Proposition 2.4.** The set of B-Fredholm elements of a unital ring `A`
modulo a two-sided ideal `J` is closed under (i) sums of two members that
annihilate each other modulo `J`, (ii) products of two members that commute
modulo `J`, and (iii) perturbation by an element of `J`. -/
theorem bFredholm_prop_2_4 (hprior : Prior) {A : Type*} [Ring A]
    (J : Ideal A) [J.IsTwoSided] (a₁ a₂ : A)
    (h₁ : a₁ ∈ bFredholm J) (h₂ : a₂ ∈ bFredholm J) :
    (a₁ * a₂ ∈ J → a₂ * a₁ ∈ J → a₁ + a₂ ∈ bFredholm J) ∧
      (a₁ * a₂ - a₂ * a₁ ∈ J → a₁ * a₂ ∈ bFredholm J) ∧
      (∀ j ∈ J, a₁ + j ∈ bFredholm J) := by
  sorry

#modelClosureOfType bFredholm_prop_2_4

#print axioms bFredholm_prop_2_4

end Tex2lean.Model

```

