import Lean

/-!
\bp Assume that $a$ is Drazin invertible in $A.$ Then there exists
$b \in A $ and $ k \in \mathbb{N}$ such that $ bab=b, ab=ba,
a^kba=a^k.$ Without loss of generality, we can assume that $k=1.$
Let us show that $ A= aA \oplus N(a).$ Since $ aba=a,$ we have $
aA= a^2 A.$ So if $x \in A,$ then $ ax= a^2t, $ with $ t\in A.$
Hence, $ a(x- at)=0$ and $ x - at \in N(a).$ Therefore, $ x= at +
(x-at).$ Moreover, if $ x \in aA \cap N(a),$  then $ x=at,t \in
A.$ Hence, $ 0= bax= abat= at=x.$   Thus, $ A = aA \oplus N(a).$
\ep
-/

section Drazin

universe u
variable {A : Type u} [Mul A] [Add A] [Sub A] [Zero A]

-- Local axiomatic behaviors matching standard Ring operations used in the proof
variable (mul_assoc : ∀ x y z : A, (x * y) * z = x * (y * z))
variable (mul_sub : ∀ x y z : A, x * (y - z) = x * y - x * z)
variable (sub_self : ∀ x : A, x - x = 0)
variable (add_sub_cancel : ∀ x y : A, x * y * x + (x - x * y * x) = x)
variable (mul_zero : ∀ x : A, x * 0 = 0)

structure IsDrazinInvertible (a : A) where
  b : A
  bab : (b * a) * b = b
  comm : a * b = b * a
  aba : (a * b) * a = a

def range_a (a : A) : Set A := { x | ∃ t, x = a * t }
def kernel_a (a : A) : Set A := { x | a * x = 0 }

theorem bFredholm_prop_2_4 (a : A) (h : IsDrazinInvertible a) :
    (∀ x : A, ∃ y ∈ range_a a, ∃ z ∈ kernel_a a, x = y + z) ∧ 
    (range_a a ∩ kernel_a a = {0}) := by
  constructor
  · intro x
    let b := h.b
    use a * b * x
    constructor
    · use b * x
    · use x - a * b * x
      constructor
      · show a * (x - a * b * x) = 0
        sorry
      · sorry
  · ext x
    constructor
    · rintro ⟨h1, h2⟩
      sorry
    · rintro rfl
      sorry

end Drazin
