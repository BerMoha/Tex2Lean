import Tex2lean.Analysis.GroupInverse

/-!
# Analysis/DrazinPower: passing between `a` and `a ^ n`

The paper says "without loss of generality, we can assume that `k = 1`"
(`authoring/theorem.tex:18`).  That reduction is this file: a Drazin inverse of `a` of
index `k` yields a *group* inverse of `a ^ (k+1)`, and conversely a group inverse of any
positive power `a ^ n` yields a Drazin inverse of `a` of index `n`.

* `exists_pow_groupInverse_of_drazinInvertible` — if `b` is a Drazin inverse of `a` of
  index `k`, then `b ^ (k+1)` is a group inverse of `a ^ (k+1)`.  The computation uses
  only that `ab = ba` is idempotent, that `a ^ (k+1) (ab) = a ^ (k+1)`, and `(ab)b = b`.
* `drazinInvertible_of_pow_groupInverse` — if `d` is a group inverse of `a ^ n` with
  `n > 0`, then `a ^ (n-1) * d` is a Drazin inverse of `a` of index `n`.  Here the
  commutation `da = ad` is supplied by `groupInverse_comm`.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- A Drazin inverse of `a` of index `k` gives a group inverse of `a ^ (k+1)`.

PAPER: authoring/theorem.tex:16-18 (the paper's "we can assume that `k = 1`"). -/
theorem exists_pow_groupInverse_of_drazinInvertible {a : A} (h : IsDrazinInvertible a) :
    ∃ (n : ℕ) (d : A), 0 < n ∧ a ^ n * d * a ^ n = a ^ n ∧ d * a ^ n * d = d ∧
      a ^ n * d = d * a ^ n := by
  obtain ⟨b, k, hb, hab, hk⟩ := h
  have hC : Commute a b := hab
  -- `ab` is idempotent, so `(ab) ^ (k+1) = ab`, i.e. `a ^ n * b ^ n = a * b`.
  have hidem : IsIdempotentElem (a * b) := by
    show a * b * (a * b) = a * b
    rw [mul_assoc, ← mul_assoc b a b, hb]
  have he : a ^ (k + 1) * b ^ (k + 1) = a * b := by
    rw [← hC.mul_pow, hidem.pow_succ_eq]
  have hpow : a ^ (k + 1) * b ^ (k + 1) = b ^ (k + 1) * a ^ (k + 1) :=
    (hC.pow_pow (k + 1) (k + 1)).eq
  -- `a ^ n * b = a ^ k`, hence `a ^ n * (a * b) = a ^ n`.
  have hanb : a ^ (k + 1) * b = a ^ k := by
    rw [pow_succ, mul_assoc, hab, ← mul_assoc, hk]
  have hself : a ^ (k + 1) * a = a * a ^ (k + 1) := (Commute.pow_self a (k + 1)).eq
  have hane : a ^ (k + 1) * (a * b) = a ^ (k + 1) := by
    calc a ^ (k + 1) * (a * b) = a ^ (k + 1) * a * b := by rw [mul_assoc]
      _ = a * a ^ (k + 1) * b := by rw [hself]
      _ = a * (a ^ (k + 1) * b) := by rw [mul_assoc]
      _ = a * a ^ k := by rw [hanb]
      _ = a ^ (k + 1) := (pow_succ' a k).symm
  refine ⟨k + 1, b ^ (k + 1), Nat.succ_pos k, ?_, ?_, hpow⟩
  · calc a ^ (k + 1) * b ^ (k + 1) * a ^ (k + 1)
        = a ^ (k + 1) * (b ^ (k + 1) * a ^ (k + 1)) := mul_assoc ..
      _ = a ^ (k + 1) * (a ^ (k + 1) * b ^ (k + 1)) := by rw [hpow]
      _ = a ^ (k + 1) * (a * b) := by rw [he]
      _ = a ^ (k + 1) := hane
  · calc b ^ (k + 1) * a ^ (k + 1) * b ^ (k + 1)
        = a ^ (k + 1) * b ^ (k + 1) * b ^ (k + 1) := by rw [hpow]
      _ = a * b * b ^ (k + 1) := by rw [he]
      _ = b * a * b ^ (k + 1) := by rw [hab]
      _ = b * a * (b * b ^ k) := by rw [← pow_succ' b k]
      _ = b * a * b * b ^ k := by simp only [mul_assoc]
      _ = b * b ^ k := by rw [hb]
      _ = b ^ (k + 1) := (pow_succ' b k).symm

/-- A group inverse of a positive power `a ^ n` makes `a` Drazin invertible, with
`a ^ (n-1) * d` as the Drazin inverse of index `n`.

PAPER: authoring/theorem.tex:36-40 (the paper's final "`aba = a, bab = b, ab = ba`"). -/
theorem drazinInvertible_of_pow_groupInverse {a d : A} {n : ℕ} (hn : 0 < n)
    (hcdc : a ^ n * d * a ^ n = a ^ n) (hdcd : d * a ^ n * d = d)
    (hcd : a ^ n * d = d * a ^ n) : IsDrazinInvertible a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  -- `d` commutes with `a`, because `a ^ (m+1)` does.
  have hda : d * a = a * d :=
    groupInverse_comm hcdc hdcd hcd (Commute.pow_self a (m + 1)).eq
  have hC : Commute d a := hda
  have hdm : d * a ^ m = a ^ m * d := (hC.pow_right m).eq
  have hcm : a ^ (m + 1) * a ^ m = a ^ m * a ^ (m + 1) :=
    (Commute.pow_pow_self a (m + 1) m).eq
  -- `b * a = a * b = a ^ (m+1) * d`.
  have hba : a ^ m * d * a = a ^ (m + 1) * d := by
    calc a ^ m * d * a = a ^ m * (d * a) := mul_assoc ..
      _ = a ^ m * (a * d) := by rw [hda]
      _ = a ^ m * a * d := (mul_assoc ..).symm
      _ = a ^ (m + 1) * d := by rw [← pow_succ]
  have hab : a * (a ^ m * d) = a ^ (m + 1) * d := by
    rw [← mul_assoc, ← pow_succ' a m]
  have hcdd : a ^ (m + 1) * d * d = d := by rw [hcd, hdcd]
  refine ⟨a ^ m * d, m + 1, ?_, ?_, ?_⟩
  · -- `b * a * b = b`
    calc a ^ m * d * a * (a ^ m * d) = a ^ (m + 1) * d * (a ^ m * d) := by rw [hba]
      _ = a ^ (m + 1) * (d * a ^ m) * d := by simp only [mul_assoc]
      _ = a ^ (m + 1) * (a ^ m * d) * d := by rw [hdm]
      _ = a ^ (m + 1) * a ^ m * (d * d) := by simp only [mul_assoc]
      _ = a ^ m * a ^ (m + 1) * (d * d) := by rw [hcm]
      _ = a ^ m * (a ^ (m + 1) * d * d) := by simp only [mul_assoc]
      _ = a ^ m * d := by rw [hcdd]
  · -- `a * b = b * a`
    rw [hab, hba]
  · -- `a ^ n * b * a = a ^ n`
    calc a ^ (m + 1) * (a ^ m * d) * a = a ^ (m + 1) * (a ^ m * d * a) := mul_assoc ..
      _ = a ^ (m + 1) * (a ^ (m + 1) * d) := by rw [hba]
      _ = a ^ (m + 1) * (d * a ^ (m + 1)) := by rw [hcd]
      _ = a ^ (m + 1) * d * a ^ (m + 1) := (mul_assoc ..).symm
      _ = a ^ (m + 1) := hcdc

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · both transfers between Drazin invertibility of `a` and group
  invertibility of `a ^ n`; fully proved
-/

end Tex2lean
