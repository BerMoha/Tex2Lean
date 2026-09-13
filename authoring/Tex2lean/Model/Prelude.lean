import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Ring.Idempotent

/-!
# Model/Prelude: the vocabulary of the theorem

Right ideals are encoded as `Submodule Aᵐᵒᵖ A`, using Mathlib's opposite-module
instance for the right action. The statement-level form of the decomposition is the
elementwise `DirectSumDecomp`, so the headline does not force the referee to accept the
`Submodule` encoding merely to parse the claim.
-/

namespace Tex2lean

variable {A : Type*} [Ring A]

/-! ## Vocabulary -/

/-- The right ideal `a * A`, as a submodule of `A` over the opposite ring. -/
def rightMul (a : A) : Submodule Aᵐᵒᵖ A where
  carrier := Set.range (fun t : A => a * t)
  add_mem' := by
    rintro _ _ ⟨t, rfl⟩ ⟨u, rfl⟩
    exact ⟨t + u, by simp [mul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    intro s x hx
    rcases hx with ⟨t, rfl⟩
    exact ⟨t * s.unop, by
      change a * (t * s.unop) = (a * t) * s.unop
      rw [mul_assoc]⟩

/-- The right annihilator `N(a) = {x | a * x = 0}`, as a right ideal. -/
def rightAnn (a : A) : Submodule Aᵐᵒᵖ A where
  carrier := {x : A | a * x = 0}
  add_mem' := by
    intro x y hx hy
    have hx' : a * x = 0 := hx
    have hy' : a * y = 0 := hy
    change a * (x + y) = 0
    rw [mul_add, hx', hy', add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro s x hx
    have hx' : a * x = 0 := hx
    change a * (x * s.unop) = 0
    rw [← mul_assoc, hx', zero_mul]

/-- `DirectSumDecomp c` says `A` is the internal direct sum of the right ideal `cA`
and the right annihilator `N(c)`, written elementwise. -/
def DirectSumDecomp (c : A) : Prop :=
  (∀ y : A, ∃ t z : A, y = c * t + z ∧ c * z = 0) ∧
  (∀ z : A, (∃ t, z = c * t) → c * z = 0 → z = 0)

/-- `b` is a Drazin inverse of `a` of index at most `k`: the three equations from the
paper, with the paper's third clause `a ^ k * b * a = a ^ k`. -/
def IsDrazinInverse (a b : A) (k : ℕ) : Prop :=
  b * a * b = b ∧ a * b = b * a ∧ a ^ k * b * a = a ^ k

/-- `b` is a group inverse of `a`: the `k = 1` special case of Drazin invertibility. -/
def IsGroupInverse (a b : A) : Prop :=
  a * b * a = a ∧ b * a * b = b ∧ a * b = b * a

/-- `a` is group invertible. The paper's proof body actually establishes the
group-invertible case, and the full result is obtained by applying it to `a ^ n`. -/
def IsGroupInvertible (a : A) : Prop := ∃ b : A, IsGroupInverse a b

/-! ## The quantity -/

/-- Drazin invertibility: the left-hand side of the equivalence the theorem proves. -/
def IsDrazinInvertible (a : A) : Prop :=
  ∃ (b : A) (k : ℕ), IsDrazinInverse a b k

end Tex2lean
