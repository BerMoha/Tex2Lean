import Mathlib.Algebra.Module.Submodule.Lattice
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.GroupInvertibleIffDirectSumDecomp
import Tex2lean.Analysis.IdempotentsOfGroupInverse

/-!
# Analysis/IdempotentsOfDirectSumDecomp

The idempotent-extraction step of the paper's converse direction, isolated from the
construction of the group inverse itself: given `A = cA ⊕ N(c)`, split `e = p + q` with
`p ∈ cA`, `q ∈ N(c)`, and show directly (from `aA ∩ N(a) = {0}` applied twice, once to
`p - p^2 = qp` and once to the symmetric statement for `q`) that `p` and `q` are
complementary idempotents with `pA` realizing `cA` and `qA` realizing `N(c)`.

This no longer needs its own splitting argument: `groupInvertible_iff_directSumDecomp`
already turns `DirectSumDecomp c` into a group inverse `b` of `c`, and
`idempotents_of_groupInverse` already builds `p = c b`, `q = 1 - p` from such a `b`. The
proof here is just the composition of those two.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- INTERNAL: composition of `groupInvertible_iff_directSumDecomp` and
`idempotents_of_groupInverse`; the paper's own passage this renders is
authoring/theorem.tex:1181-1187, already carried in full by `idempotents_of_groupInverse`.
From `A = cA ⊕ N(c)`, obtain idempotents `p, q` with `p + q = 1`, `p * q = q * p = 0`,
`A = pA ⊕ qA`, and in fact `pA = cA` and `N(c) = qA`. -/
theorem idempotents_of_directSumDecomp (c : A) (h : DirectSumDecomp c) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  obtain ⟨b, hb⟩ := (groupInvertible_iff_directSumDecomp c).mpr h
  exact idempotents_of_groupInverse c b hb

end Tex2lean
