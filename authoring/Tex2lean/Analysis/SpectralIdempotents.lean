import Tex2lean.Analysis.GroupInverse
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Analysis/SpectralIdempotents: the two idempotents of the splitting

The second claim of the paper (`authoring/theorem.tex:10-12`): when `A = cA ⊕ N(c)` there
are idempotents `p, q` with `e = p + q`, `pq = qp = 0` and `A = pA ⊕ qA`.

The paper extracts `p` and `q` from the decomposition of `e` itself.  Here they are built
from the group inverse `d` of `c` supplied by `Analysis/GroupInverse`, as `p = cd` and
`q = e - cd`; that is the same pair — the paper's own argument shows its `p` equals `ab`
(`authoring/theorem.tex:34-36`) — and it makes the two extra equalities
`pA = cA` and `N(c) = qA` immediate, which is what turns the idempotent claim from a
vacuous one (`p = e, q = 0` satisfies the bare conditions) into the paper's.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- From a group inverse `d` of `c`, the paper's two idempotents `p = cd` and `q = e - cd`,
together with `pA = cA` and `N(c) = qA`.

PAPER: authoring/theorem.tex:10-12 and 26-36. -/
theorem exists_idempotents_of_groupInverse {c d : A} (hcdc : c * d * c = c)
    (hcd : c * d = d * c) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  -- `p = cd` is idempotent, `pc = c` and `cp = c`.
  have hp : c * d * (c * d) = c * d := by rw [← mul_assoc, hcdc]
  have hcp : c * (c * d) = c := by rw [hcd, ← mul_assoc, hcdc]
  have hpq : c * d * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have hqp : (1 - c * d) * (c * d) = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hcq : c * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hcp, sub_self]
  refine ⟨c * d, 1 - c * d, hp, ?_, by abel, hpq, hqp, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `q` is idempotent
    show (1 - c * d) * (1 - c * d) = 1 - c * d
    rw [mul_sub, mul_one, hqp, sub_zero]
  · -- `pA ⊓ qA = ⊥`
    refine Submodule.disjoint_def.mpr ?_
    rintro x ⟨u, rfl⟩ ⟨v, hv⟩
    have hv' : (1 - c * d) * v = c * d * u := hv
    have h1 : c * d * (c * d * u) = c * d * u := by rw [← mul_assoc, hp]
    have h2 : c * d * (c * d * u) = 0 := by rw [← hv', ← mul_assoc, hpq, zero_mul]
    exact h1.symm.trans h2
  · -- `pA ⊔ qA = ⊤`
    intro s hps hqs x _
    have h1 : c * d * x ∈ s := hps ⟨x, rfl⟩
    have h2 : (1 - c * d) * x ∈ s := hqs ⟨x, rfl⟩
    have hx : c * d * x + (1 - c * d) * x = x := by
      rw [← add_mul]; simp
    exact hx ▸ s.add_mem h1 h2
  · -- `pA = cA`
    refine le_antisymm ?_ ?_
    · rintro x ⟨t, rfl⟩
      exact ⟨d * t, by show c * (d * t) = c * d * t; rw [← mul_assoc]⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨c * t, by show c * d * (c * t) = c * t; rw [← mul_assoc, hcdc]⟩
  · -- `N(c) = qA`
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : c * x = 0 := hx
      refine ⟨x, ?_⟩
      show (1 - c * d) * x = x
      rw [sub_mul, one_mul, hcd, mul_assoc, hx', mul_zero, sub_zero]
    · rintro x ⟨t, rfl⟩
      show c * ((1 - c * d) * t) = 0
      rw [← mul_assoc, hcq, zero_mul]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · the idempotent pair `cd`, `e - cd` with all six conditions; fully proved
-/

end Tex2lean
