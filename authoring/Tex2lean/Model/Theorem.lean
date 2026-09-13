import Tex2lean.Model.Prior
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.TheoremProof
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Model/Theorem: the theorem

This is the single capstone statement of the development.  It packages the two
claims of the paper into one theorem over the real objects defined in
`Model/Prelude`, with the empty `Prior` assumption carried as the first
hypothesis as required by the audit-surface discipline.

The first conjunct is the equivalence: Drazin invertibility of `a` is equivalent
to the existence of a positive power `a ^ n` whose right-multiple ideal and right
annihilator split `A`.  The second conjunct is the strengthened (non-vacuous)
idempotent form: from such a splitting at `n`, one obtains idempotents `p` and `q`
with `p + q = 1`, `p*q = q*p = 0`, `A = pA ⊕ qA`, and in fact `pA = (a^n)A` and
`qA = N(a^n)`.  The last two equalities are what make the idempotent claim
non-vacuous.

The statement is written over `[Ring A]`, not `[CommRing A]`: the argument never
uses commutativity of the ambient ring, only that `a` commutes with its Drazin
inverse.

The proof is `Tex2lean.drazin_characterization_proof` in `Analysis/TheoremProof`,
which chains the pivot `A = cA ⊕ N(c) ↔ c is group invertible`
(`Analysis/GroupInverse`) through the paper's reduction to `k = 1`
(`Analysis/DrazinPower`) and the idempotent pair `p = cd`, `q = e - cd`
(`Analysis/SpectralIdempotents`).
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- The capstone theorem: the Drazin invertibility equivalence together with the
strengthened spectral idempotent decomposition. -/
theorem drazin_characterization (hprior : Prior) (a : A) :
    (IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n)) ∧
    (∀ n : ℕ, 0 < n → DirectSumDecomp (a ^ n) →
      ∃ p q : A,
        IsIdempotentElem p ∧ IsIdempotentElem q ∧
          p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
          IsCompl (rightMul p) (rightMul q) ∧
          rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q) :=
  drazin_characterization_proof a

#print axioms drazin_characterization

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · closed by `drazin_characterization_proof`; axioms are exactly
  `propext`, `Classical.choice`, `Quot.sound`
-/

end Tex2lean
