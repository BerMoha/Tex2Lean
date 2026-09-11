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
