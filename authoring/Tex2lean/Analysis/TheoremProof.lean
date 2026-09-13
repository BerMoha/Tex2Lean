import Tex2lean.Analysis.DrazinPower
import Tex2lean.Analysis.SpectralIdempotents

/-!
# Analysis/TheoremProof: assembling the capstone

The paper's theorem (`authoring/theorem.tex:6-13`) makes two claims about an element `a`
of a unital ring `A`:

* the equivalence — `a` is Drazin invertible iff some positive power `a ^ n` splits `A`
  as `a^n A ⊕ N(a^n)`;
* the idempotent consequence — in that case there are idempotents `p`, `q` with
  `e = p + q`, `pq = qp = 0` and `A = pA ⊕ qA`, realized here in the strengthened form
  `pA = (a^n)A` and `qA = N(a^n)`.

Both are routed through the single pivot of the argument, proved in
`Analysis/GroupInverse`: for one fixed element `c`, the splitting `A = cA ⊕ N(c)` is the
same thing as `c` having a group inverse.  `Analysis/DrazinPower` moves that pivot between
`a` and `a ^ n` — which is the paper's "without loss of generality `k = 1`" — and
`Analysis/SpectralIdempotents` reads the idempotents `p = cd`, `q = e - cd` off the group
inverse.

This file carries no ring computation of its own; it only chains those four lemmas into
the conjunction the audit surface states.  The `Prior` hypothesis of the capstone is empty
and is not used.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- The two claims of the paper's theorem, packaged as one conjunction: the Drazin
equivalence together with the strengthened spectral idempotent decomposition at every
positive power that splits.

PAPER: authoring/theorem.tex:6-13 -/
theorem drazin_characterization_proof (a : A) :
    (IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n)) ∧
    (∀ n : ℕ, 0 < n → DirectSumDecomp (a ^ n) →
      ∃ p q : A,
        IsIdempotentElem p ∧ IsIdempotentElem q ∧
          p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
          IsCompl (rightMul p) (rightMul q) ∧
          rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q) := by
  constructor
  · constructor
    · intro h
      obtain ⟨n, d, hn, hcdc, _, hcd⟩ := exists_pow_groupInverse_of_drazinInvertible h
      exact ⟨n, hn, directSumDecomp_of_groupInverse hcdc hcd⟩
    · rintro ⟨n, hn, hdec⟩
      obtain ⟨d, hcdc, hdcd, hcd⟩ := groupInverse_of_directSumDecomp hdec
      exact drazinInvertible_of_pow_groupInverse hn hcdc hdcd hcd
  · intro n _ hdec
    obtain ⟨d, hcdc, _, hcd⟩ := groupInverse_of_directSumDecomp hdec
    exact exists_idempotents_of_groupInverse hcdc hcd

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · capstone assembled from `Analysis/GroupInverse`,
  `Analysis/DrazinPower` and `Analysis/SpectralIdempotents`; no `sorry`.  The route
  through `Model/Pseudocode` was abandoned: `Model/Pseudocode` imports
  `Analysis/PseudocodeProof`, which imports `Model/Theorem`, so importing it here is a
  module cycle — and that file derives the Pseudocode statements *from* this capstone.
-/

end Tex2lean
