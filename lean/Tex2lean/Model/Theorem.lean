import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs

/-!
\bp Assume that $a$ is Drazin invertible in $A.$ Then there exists
$b \in A $ and $ k \in \mathbb{N}$ such that $ bab=b, ab=ba,
a^kba=a^k.$ Without lose of generality, we can assume that $k=1.$
Let us show that $ A= aA \oplus N(a).$ Since $ aba=a,$ we have $
aA= a^2 A.$ So if $x \in A,$ then $ ax= a^2t, $ with $ t\in A.$
Hence, $ a(x- at)=0$ and $ x - at \in N(a).$ Therefore, $ x= at +
(x-at).$ Moreover, if $ x \in aA \cap N(a),$  then $ x=at,t \in
A.$ Hence, $ 0= bax= abat= at=x.$   Thus, $ A = aA \oplus N(a).$
\ep
-/

section Drazin

variable {A : Type*} [Ring A]

/-- Formal definition of Drazin invertibility for an element `a` with index `k = 1` -/
structure IsDrazinInvertible (a : A) where
  b : A
  bab : b * a * b = b
  comm : a * b = b * a
  aba : a * b * a = a

/-- Definitions of the range of `a` (aA) and the kernel/nullspace of `a` (N(a)) --/
def range_a (a : A) : Set A := { x | ∃ t, x = a * t }
def kernel_a (a : A) : Set A := { x | a * x = 0 }

/-- Theorem 2.4: A ring A decomposes into a direct sum of aA and N(a) 
    if and only if `a` is Drazin invertible. -/
theorem bFredholm_prop_2_4 (a : A) (h : IsDrazinInvertible a) :
    (∀ x : A, ∃ y ∈ range_a a, ∃ z ∈ kernel_a a, x = y + z) ∧ 
    (range_a a ∩ kernel_a a = {0}) := by
  constructor
  · intro x
    -- Extract the element `b` provided by the Drazin hypothesis
    let b := h.b
    use a * b * x
    constructor
    · use b * x
      assoc_rw [h.aba]
    · use x - a * b * x
      constructor
      · show a * (x - a * b * x) = 0
        rw [mul_sub, ← mul_assoc, h.aba, sub_self]
      · rw [add_sub_cancel]
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, hx2⟩
      let b := h.b
      have h1 : b * a * (a * t) = 0 := by rw [← mul_assoc, hx2, mul_zero]
      have h2 : a * t = 0 := by
        calc a * t = (a * b * a) * t := by rw [h.aba]
        _ = a * (b * a * (a * t)) := by ring
        _ = a * 0 := by rw [h1]
        _ = 0 := by rw [mul_zero]
      exact h2
    · rintro rfl
      constructor
      · use 0
        rw [mul_zero]
      · rw [mul_zero]

end Drazin
