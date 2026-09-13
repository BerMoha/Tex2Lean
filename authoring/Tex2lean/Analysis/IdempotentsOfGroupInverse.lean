import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.NoncommRing
import Tex2lean.Model.Prelude

/-!
# Analysis/IdempotentsOfGroupInverse

PAPER: authoring/theorem.tex:1181-1187 (the converse direction's spectral idempotents,
built directly from a group inverse rather than from `DirectSumDecomp`).

Given a group inverse `b` of `c` (`c b c = c`, `b c b = b`, `c b = b c`), the paper's
idempotents are `p = c b`, `q = e - p`. This is the same construction the paper's
converse direction ends with, but phrased as a direct consequence of group
invertibility, so it can be composed with `groupInvertible_iff_directSumDecomp` to
prove `idempotents_of_directSumDecomp` without re-deriving the splitting of `A`.

`p * p = p` is immediate from `c b c = c`: `(c b)(c b) = (c b c) b = c b = p`. From there
`q * q = q` is pure additive algebra. `p A = c A` uses `c b c = c` again (`p c = c`, so
`c t = p (c t)`) together with the trivial inclusion `p t = c (b t)`. `N(c) = q A` uses
commutativity `c b = b c` as well: `c p = c b c = c`, hence `c q = 0`, giving one
inclusion, and for the other, `c b = b c` gives `p x = b (c x)` for `x ∈ N(c)`, so
`p x = 0` and `x = q x`. Complementarity of `p A` and `q A` is then formal from
`p * p = p`, `p * q = 0`, `p + q = 1`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- PAPER: authoring/theorem.tex:1181-1187. From a group inverse `b` of `c`, the
idempotents `p = c b`, `q = 1 - p` split `1`, are complementary, and realize `c A` and
`N(c)` respectively. -/
theorem idempotents_of_groupInverse (c b : A) (hb : IsGroupInverse c b) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  obtain ⟨h1, h2, h3⟩ := hb
  -- h1 : c * b * c = c, h2 : b * c * b = b, h3 : c * b = b * c
  set p := c * b with hp_def
  set q := (1 : A) - p with hq_def
  have hpp : p * p = p := by
    show (c * b) * (c * b) = c * b
    rw [← mul_assoc (c * b) c b, h1]
  have hpc : p * c = c := h1
  have hcomm : c * b = b * c := hp_def.symm.trans h3
  have hcp : c * p = c := by
    show c * (c * b) = c
    rw [hcomm, ← mul_assoc]
    exact h1
  have hqq : q * q = q := by
    have expand : q * q = 1 - p - p + p * p := by
      show (1 - p) * (1 - p) = 1 - p - p + p * p
      noncomm_ring
    rw [expand, hpp]
    show (1 : A) - p - p + p = 1 - p
    noncomm_ring
  have hpq : p + q = 1 := by
    show p + (1 - p) = 1
    noncomm_ring
  have hpq0 : p * q = 0 := by
    have expand : p * q = p - p * p := by
      show p * (1 - p) = p - p * p
      noncomm_ring
    rw [expand, hpp, sub_self]
  have hqp0 : q * p = 0 := by
    have expand : q * p = p - p * p := by
      show (1 - p) * p = p - p * p
      noncomm_ring
    rw [expand, hpp, sub_self]
  -- rightMul p = rightMul c
  have hrm : rightMul p = rightMul c := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      exact ⟨b * t, (mul_assoc c b t).symm⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨c * t, ?_⟩
      show p * (c * t) = c * t
      rw [← mul_assoc, hpc]
  -- rightAnn c = rightMul q
  have hra : rightAnn c = rightMul q := by
    apply le_antisymm
    · intro x hx
      have hcx : c * x = 0 := hx
      have hpx : p * x = 0 := by
        have hbcx : p * x = b * (c * x) := by
          show (c * b) * x = b * (c * x)
          rw [hcomm, mul_assoc]
        rw [hbcx, hcx, mul_zero]
      have hxq : x = q * x := by
        show x = (1 - p) * x
        rw [sub_mul, one_mul, hpx, sub_zero]
      exact ⟨x, hxq.symm⟩
    · rintro _ ⟨t, rfl⟩
      have hcq : c * q = 0 := by
        show c * (1 - p) = 0
        rw [mul_sub, mul_one, hcp, sub_self]
      show c * (q * t) = 0
      rw [← mul_assoc, hcq, zero_mul]
  refine ⟨p, q, hpp, hqq, hpq, hpq0, hqp0, ?_, hrm, hra⟩
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨s, rfl⟩ ⟨t, hxt⟩
    have hxt' : q * t = p * s := hxt
    have e1 : p * (p * s) = p * s := by rw [← mul_assoc, hpp]
    have e2 : p * (p * s) = p * (q * t) := by rw [hxt']
    have e3 : p * (q * t) = 0 := by
      have : p * (q * t) = (p * q) * t := (mul_assoc p q t).symm
      rw [this, hpq0, zero_mul]
    rw [e3] at e2
    rw [e2] at e1
    exact e1.symm
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x = p * x + q * x := by
      have hstep : (p + q) * x = 1 * x := by rw [hpq]
      rw [add_mul, one_mul] at hstep
      exact hstep.symm
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

end Tex2lean
