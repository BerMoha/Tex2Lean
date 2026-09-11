import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Abel

/-!
# Drazin Invertibility — Proposition 2.4

Assume that `a` is Drazin invertible in `A`. Then there exists `b ∈ A` and `k ∈ ℕ`
such that `bab = b`, `ab = ba`, `aᵏba = aᵏ`. With `k = 1`, we show `A = aA ⊕ N(a)`.
-/

section Drazin

variable {A : Type*} [Ring A]

structure IsDrazinInvertible (a : A) where
  b : A
  bab : b * a * b = b
  comm : a * b = b * a
  aba : a * b * a = a

def range_a (a : A) : Set A := { x | ∃ t, x = a * t }
def kernel_a (a : A) : Set A := { x | a * x = 0 }

theorem bFredholm_prop_2_4 (a : A) (h : IsDrazinInvertible a) :
    (∀ x : A, ∃ y ∈ range_a a, ∃ z ∈ kernel_a a, x = y + z) ∧
    (range_a a ∩ kernel_a a = {0}) := by
  constructor
  · intro x
    use a * h.b * x
    constructor
    · exact ⟨h.b * x, mul_assoc a h.b x⟩
    · use x - a * h.b * x
      constructor
      · show a * (x - a * h.b * x) = 0
        have key : a * (a * h.b) = a := by
          rw [h.comm, ← mul_assoc]; exact h.aba
        rw [mul_sub, ← mul_assoc a (a * h.b) x, key, sub_self]
      · abel
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, hx2⟩
      have h1 : (h.b * a) * (a * t) = 0 := by
        rw [mul_assoc h.b a (a * t), hx2, mul_zero]
      calc a * t = (a * h.b * a) * t := by rw [h.aba]
        _ = (a * h.b) * (a * t) := by rw [mul_assoc (a * h.b) a t]
        _ = (h.b * a) * (a * t) := by rw [h.comm]
        _ = 0 := h1
    · rintro rfl
      exact ⟨⟨0, by rw [mul_zero]⟩, by rw [mul_zero]⟩

end Drazin
