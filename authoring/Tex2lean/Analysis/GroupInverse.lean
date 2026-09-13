import Tex2lean.Model.Prelude
import Mathlib.Tactic.Abel

/-!
# Analysis/GroupInverse: the splitting is exactly group invertibility

The whole of the paper's argument (`authoring/theorem.tex:15-40`) turns on one
equivalence, stated here for a single ring element `c`:

  `DirectSumDecomp c`  ↔  `c` has a group inverse.

Both directions are the paper's own, transcribed for `c` in place of the paper's `a`
(the paper says "without loss of generality we can assume `k = 1`"; the reduction that
justifies that is carried out on `c = a ^ n` in `Analysis/DrazinPower`).

* `directSumDecomp_of_groupInverse` is the paper's first half: `x = c(dx) + (x - cdx)`
  gives existence, and `x ∈ cA ∩ N(c) → x = 0` follows from `cdc = c`.
* `groupInverse_of_directSumDecomp` is the paper's second half: split `e = p + q`,
  show `p` is idempotent, `cp = pc = c`, then use `cA = c²A` to write `p = cb` and check
  `cbc = c`, `bc = p`, `bcb = b`.
* `groupInverse_comm` is the standard fact that a group inverse commutes with everything
  its element commutes with.  The paper uses it silently when it passes between `a` and
  `a ^ n`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- Unfolding of membership in the right ideal `cA`.

INTERNAL: `rightMul` is defined by a `Set.range` carrier; this is the `Iff` that the
lattice arguments in `Analysis/SpectralIdempotents` rewrite with. -/
theorem mem_rightMul {c x : A} : x ∈ rightMul c ↔ ∃ t, c * t = x := Iff.rfl

/-- Unfolding of membership in the right annihilator `N(c)`.

INTERNAL: companion to `mem_rightMul`. -/
theorem mem_rightAnn {c x : A} : x ∈ rightAnn c ↔ c * x = 0 := Iff.rfl

/-! ## From a group inverse to the splitting -/

/-- If `c` has a group inverse `d` then `A = cA ⊕ N(c)`.

PAPER: authoring/theorem.tex:16-24 (the forward half, with `d` for the paper's `b`). -/
theorem directSumDecomp_of_groupInverse {c d : A} (hcdc : c * d * c = c)
    (hcd : c * d = d * c) : DirectSumDecomp c := by
  have hccd : c * (c * d) = c := by
    rw [hcd, ← mul_assoc, hcdc]
  refine ⟨fun y => ⟨d * y, y - c * (d * y), by abel, ?_⟩, ?_⟩
  · have h : c * (c * (d * y)) = c * y := by
      calc c * (c * (d * y)) = c * (c * d) * y := by simp [mul_assoc]
        _ = c * y := by rw [hccd]
    rw [mul_sub, h, sub_self]
  · rintro z ⟨t, rfl⟩ hz
    calc c * t = c * d * c * t := by rw [hcdc]
      _ = d * (c * (c * t)) := by rw [hcd]; simp [mul_assoc]
      _ = 0 := by rw [hz, mul_zero]

/-! ## From the splitting to a group inverse -/

/-- If `A = cA ⊕ N(c)` then `c` has a group inverse.

PAPER: authoring/theorem.tex:26-39 (the converse half, with `c` for the paper's `a`). -/
theorem groupInverse_of_directSumDecomp {c : A} (h : DirectSumDecomp c) :
    ∃ d : A, c * d * c = c ∧ d * c * d = d ∧ c * d = d * c := by
  obtain ⟨hex, huniq⟩ := h
  -- `e = p + q` with `p = c * t ∈ cA` and `q ∈ N(c)`.
  obtain ⟨t, q, h1, hcq⟩ := hex 1
  have hq : q = 1 - c * t := by rw [h1]; abel
  -- `cp = c`, since `cq = 0`.
  have hcp : c * (c * t) = c := by
    have h2 : c * (c * t + q) = c * 1 := by rw [← h1]
    rw [mul_add, hcq, add_zero, mul_one] at h2
    exact h2
  -- `qc ∈ cA ∩ N(c)`, hence `qc = 0` and `pc = c`.
  have hqc : q * c = 0 := by
    refine huniq (q * c) ⟨1 - t * c, ?_⟩ ?_
    · rw [hq, sub_mul, one_mul, mul_sub, mul_one, mul_assoc]
    · rw [← mul_assoc, hcq, zero_mul]
  have hpc : c * t * c = c := by
    have h2 : (c * t + q) * c = 1 * c := by rw [← h1]
    rw [add_mul, hqc, add_zero, one_mul] at h2
    exact h2
  -- `cA = c²A`, so `p = c * b` with `b ∈ cA`.
  obtain ⟨t', z, h2, hcz⟩ := hex t
  refine ⟨c * t', ?_, ?_, ?_⟩ <;>
    (have hpb : c * t = c * (c * t') := by
      calc c * t = c * (c * t' + z) := by rw [← h2]
        _ = c * (c * t') + c * z := by rw [mul_add]
        _ = c * (c * t') := by rw [hcz, add_zero])
  · -- `c * b * c = c`
    rw [← hpb]; exact hpc
  · -- `b * c * b = b`, via `q * b = 0`
    have hqb : q * (c * t') = 0 := by
      refine huniq _ ⟨t' - t * (c * t'), ?_⟩ ?_
      · rw [hq, sub_mul, one_mul, mul_sub, mul_assoc]
      · rw [← mul_assoc, hcq, zero_mul]
    have hbc : c * t' * c = c * t := by
      have hsub : c * t' * c - c * t = 0 := by
        refine huniq _ ⟨t' * c - t, ?_⟩ ?_
        · rw [mul_sub, ← mul_assoc]
        · rw [mul_sub, sub_eq_zero]
          calc c * (c * t' * c) = c * (c * t') * c := by simp [mul_assoc]
            _ = c * t * c := by rw [← hpb]
            _ = c := hpc
            _ = c * (c * t) := hcp.symm
      exact sub_eq_zero.mp hsub
    have hpbb : c * t * (c * t') = c * t' := by
      have h3 : (c * t + q) * (c * t') = 1 * (c * t') := by rw [← h1]
      rw [add_mul, hqb, add_zero, one_mul] at h3
      exact h3
    rw [hbc]; exact hpbb
  · -- `c * b = b * c`, both equal `p`
    have hbc : c * t' * c = c * t := by
      have hsub : c * t' * c - c * t = 0 := by
        refine huniq _ ⟨t' * c - t, ?_⟩ ?_
        · rw [mul_sub, ← mul_assoc]
        · rw [mul_sub, sub_eq_zero]
          calc c * (c * t' * c) = c * (c * t') * c := by simp [mul_assoc]
            _ = c * t * c := by rw [← hpb]
            _ = c := hpc
            _ = c * (c * t) := hcp.symm
      exact sub_eq_zero.mp hsub
    rw [hbc, hpb]

/-! ## The group inverse commutes with the commutant -/

/-- A group inverse `d` of `c` commutes with every element that `c` commutes with.

PAPER: authoring/theorem.tex:15-40 — used silently by the paper when it moves between
`a` and its Drazin inverse; `INTERNAL` in the sense that the paper never states it, but
the paper's `ab = ba` clause is exactly this fact for `x = a`. -/
theorem groupInverse_comm {c d x : A} (hcdc : c * d * c = c) (hdcd : d * c * d = d)
    (hcd : c * d = d * c) (hx : c * x = x * c) : d * x = x * d := by
  have hcdd : c * d * d = d := by rw [hcd, hdcd]
  have hddc : d * d * c = d := by rw [mul_assoc, ← hcd, ← mul_assoc, hdcd]
  have e1 : d * d * (x * c) = d * x := by rw [← hx, ← mul_assoc, hddc]
  have e2 : c * x * (d * d) = x * d := by
    rw [hx, mul_assoc, ← mul_assoc c d d, hcdd]
  have h1 : d * x * (d * c) = d * x := by
    calc d * x * (d * c) = d * d * (x * c) * (d * c) := by rw [e1]
      _ = d * d * (x * (c * d * c)) := by simp [mul_assoc]
      _ = d * d * (x * c) := by rw [hcdc]
      _ = d * x := e1
  have h2 : c * d * (x * d) = x * d := by
    calc c * d * (x * d) = c * d * (c * x * (d * d)) := by rw [e2]
      _ = c * d * c * x * (d * d) := by simp [mul_assoc]
      _ = c * x * (d * d) := by rw [hcdc]
      _ = x * d := e2
  calc d * x = d * x * (d * c) := h1.symm
    _ = d * (x * c) * d := by rw [← hcd]; simp [mul_assoc]
    _ = d * (c * x) * d := by rw [hx]
    _ = c * d * (x * d) := by rw [hcd]; simp [mul_assoc]
    _ = x * d := h2

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · both directions of `DirectSumDecomp c ↔ c group invertible`, plus the
  commutation lemma; fully proved
-/

end Tex2lean
