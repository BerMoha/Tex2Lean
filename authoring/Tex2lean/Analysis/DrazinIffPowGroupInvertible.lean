import Tex2lean.Model.Prelude
import Tex2lean.Analysis.GroupInvertibleIffDirectSumDecomp
import Tex2lean.Analysis.PseudocodeProof

/-!
# Analysis/DrazinIffPowGroupInvertible

The "without loss of generality `k = 1`" step of the paper's proof, stated as its own
equivalence: `a` is Drazin invertible (via some `b` and index `k`) exactly when some
positive power `a ^ n` is group invertible.

Forward: from `b a b = b`, `a b = b a`, `a ^ k * b * a = a ^ k`, take `n = k` (or `n = 1`
if `k = 0`, since `a ^ 0 = 1` is its own group inverse) and show `a ^ n` has group
inverse `b ^ n`.

Backward: if `a ^ n` has group inverse `d`, then `a` is Drazin invertible with index
`n`, using a Drazin inverse built from `d` and powers of `a`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- `a` is Drazin invertible iff some positive power of `a` is group invertible. This is
the paper's reduction "we can assume `k = 1`" made precise: applying the `k = 1` case to
`a ^ n` in place of `a` recovers the general statement. -/
theorem drazin_iff_exists_pow_groupInvertible (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ IsGroupInvertible (a ^ n) := by
  rw [drazin_iff_exists_power_decomp' a]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (groupInvertible_iff_directSumDecomp (a ^ n)).2 h⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (groupInvertible_iff_directSumDecomp (a ^ n)).1 h⟩

end Tex2lean
