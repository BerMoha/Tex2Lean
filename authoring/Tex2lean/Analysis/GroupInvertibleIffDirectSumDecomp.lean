import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Tex2lean.Model.Prelude

/-!
# Analysis/GroupInvertibleIffDirectSumDecomp

The heart of the paper's argument, for a single element `c` (the case the paper calls
`k = 1`, i.e. `n = 1` applied to `c` in place of `a`): `c` has a group inverse exactly
when `A` splits as the direct sum of `cA` and `N(c)`.

Forward (paper, first paragraph): from `b` with `c b c = c`, `b c b = b`, `c b = b c`,
show `A = cA ⊕ N(c)`: `cA = c^2 A` since `c b c = c`, so every `x` splits as `c(bx) +
(x - c(bx))` with `c(x - c(bx)) = 0`; and the intersection `cA ∩ N(c)` is trivial since
`x = ct ∈ N(c)` gives `x = b c x = 0`.

Backward (paper, second paragraph): from `A = cA ⊕ N(c)`, build the idempotents `p, q`
splitting `e = p + q` with `p ∈ cA`, `q ∈ N(c)`, show `cp = pc = c`, `cq = qc = 0`, and
then (using `cA = c^2A` again) find `b ∈ cA` with `p = cb`, `cb = bc = p`, and finally
`cbc = c`, `bcb = b`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- `c` has a group inverse iff `A` is the direct sum of the right ideal `cA` and the
right annihilator `N(c)`. This is the paper's core argument, stated for a single
element; the general theorem is obtained by applying it to `c = a ^ n`. -/
theorem groupInvertible_iff_directSumDecomp (c : A) :
    IsGroupInvertible c ↔ DirectSumDecomp c := by
  constructor
  · rintro ⟨b, hb1, hb2, hb3⟩
    -- hb1 : c * b * c = c, hb2 : b * c * b = b, hb3 : c * b = b * c
    have hccb : c * c * b = c := by
      rw [mul_assoc, hb3, ← mul_assoc]; exact hb1
    have hbcc : b * c * c = c := by
      rw [← hb3]; exact hb1
    constructor
    · intro y
      refine ⟨b * y, y - c * (b * y), ?_, ?_⟩
      · abel
      · have step1 : c * (c * (b * y)) = c * y := by
          rw [← mul_assoc, ← mul_assoc, hccb]
        show c * (y - c * (b * y)) = 0
        rw [mul_sub, step1, sub_self]
    · rintro z ⟨t, rfl⟩ hz
      -- hz : c * (c * t) = 0
      have step2 : b * (c * (c * t)) = c * t := by
        simp only [← mul_assoc]
        rw [hbcc]
      rw [← step2, hz, mul_zero]
  · rintro ⟨hsum, hint⟩
    obtain ⟨t, w, h1, hcw⟩ := hsum 1
    -- h1 : (1 : A) = c * t + w, hcw : c * w = 0
    set e := c * t with he
    have hw : w = 1 - e := by rw [h1]; abel
    have hce : c * e = c := by
      have hcw' : c * (1 - e) = 0 := by rw [← hw]; exact hcw
      rw [mul_sub, mul_one, sub_eq_zero] at hcw'
      exact hcw'.symm
    have hcet : c * c * t = c * e := by rw [he, mul_assoc]
    -- e is idempotent
    have hidem : e * e = e := by
      have hu : e - e * e = c * (t * (1 - e)) := by
        rw [he]; noncomm_ring
      have hcu : c * (t * (1 - e)) = 0 := by
        have key : c * (c * (t * (1 - e))) = 0 := by
          rw [← mul_assoc, ← mul_assoc, hcet, hce, mul_sub, mul_one, hce, sub_self]
        exact hint (c * (t * (1 - e))) ⟨t * (1 - e), rfl⟩ key
      have : e - e * e = 0 := by rw [hu, hcu]
      exact sub_eq_zero.mp this |>.symm
    -- e * c = c
    have hec : e * c = c := by
      have hv : e * c - c = c * (t * c - 1) := by
        rw [he]; noncomm_ring
      have hcv : c * (t * c - 1) = 0 := by
        have key : c * (c * (t * c - 1)) = 0 := by
          rw [← mul_assoc, mul_sub, mul_one, ← mul_assoc, hcet, hce, sub_self]
        exact hint (c * (t * c - 1)) ⟨t * c - 1, rfl⟩ key
      have hv0 : e * c - c = 0 := by rw [hv, hcv]
      exact sub_eq_zero.mp hv0
    -- annihilator implication: if c * x = 0 then e * x = 0
    have ann1 : ∀ x, c * x = 0 → e * x = 0 := by
      intro x hx
      have hz_eq : e * x = c * (t * x) := by rw [he, mul_assoc]
      have hcz : c * (e * x) = 0 := by rw [← mul_assoc, hce]; exact hx
      exact hint (e * x) ⟨t * x, hz_eq⟩ hcz
    have het : e * (t * c - e) = 0 := by
      have hcz : c * (t * c - e) = 0 := by
        rw [mul_sub, ← mul_assoc, ← he, hec, hce, sub_self]
      exact ann1 (t * c - e) hcz
    have hetc : e * t * c = e := by
      rw [mul_sub] at het
      rw [hidem] at het
      rw [← mul_assoc] at het
      exact sub_eq_zero.mp het
    -- the group inverse candidate
    refine ⟨e * t, ?_, ?_, ?_⟩
    · -- c * (e * t) * c = c
      have step : c * (e * t) = e := by rw [← mul_assoc, hce, ← he]
      rw [step, hec]
    · -- (e * t) * c * (e * t) = e * t
      have step : e * t * c = e := hetc
      rw [step, ← mul_assoc, hidem]
    · -- c * (e * t) = (e * t) * c
      have step : c * (e * t) = e := by rw [← mul_assoc, hce, ← he]
      rw [step, hetc]

end Tex2lean
