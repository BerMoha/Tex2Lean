import Mathlib.Algebra.Module.Submodule.Lattice
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.PseudocodeProof

/-!
# Model/Pseudocode: theorem statements

There is no algorithm in this paper — it is a pure equivalence theorem in ring theory.
For the audit surface, this file plays the role of transcription: it records the two
claims the theorem makes over the vocabulary from `Prelude`, with no proofs.  The
proofs are assembled from `Analysis/`.

The statements use the elementwise `DirectSumDecomp` spelling for the first claim, as
recommended, and the idempotent claim is stated in its strengthened (non-vacuous) form:
the splitting idempotent `p` realizes `(a^n)A`, and its complement `q` realizes `N(a^n)`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- The headline equivalence: Drazin invertibility exactly means some positive power `a^n`
splits `A` as the direct sum of its right-multiple ideal and its right annihilator. -/
theorem drazin_iff_exists_power_decomp (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n) :=
  drazin_iff_exists_power_decomp' a

/-- The strengthened idempotent form: from a splitting at a positive power `n`, obtain
idempotents `p` and `q` with `p + q = 1`, `p*q = q*p = 0`, `A = pA ⊕ qA`, and in fact
`pA = (a^n)A` and `qA = N(a^n)`.  The last two equalities are what make the claim
non-vacuous. -/
theorem exists_spectral_idempotents (a : A) {n : ℕ} (hn : 0 < n)
    (h : DirectSumDecomp (a ^ n)) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q :=
  exists_spectral_idempotents' a hn h

end Tex2lean
