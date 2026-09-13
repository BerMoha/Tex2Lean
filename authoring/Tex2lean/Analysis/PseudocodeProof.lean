import Tex2lean.Model.Prior
import Tex2lean.Model.Theorem

/-!
# Analysis/PseudocodeProof: closing the two headline statements

Both statements in `Model/Pseudocode.lean` are direct projections of the single
capstone `Tex2lean.drazin_characterization`, so the work here is bookkeeping
extraction rather than new mathematics.

### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · closed both projections from `drazin_characterization`
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- PAPER: authoring/theorem.tex (statement of the theorem) -/
theorem drazin_iff_exists_power_decomp' (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n) :=
  (drazin_characterization ⟨⟩ a).1

/-- PAPER: authoring/theorem.tex (statement of the theorem, idempotent form) -/
theorem exists_spectral_idempotents' (a : A) {n : ℕ} (hn : 0 < n)
    (h : DirectSumDecomp (a ^ n)) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q :=
  (drazin_characterization ⟨⟩ a).2 n hn h

end Tex2lean
