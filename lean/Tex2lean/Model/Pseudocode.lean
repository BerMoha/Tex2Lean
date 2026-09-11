import Tex2lean.Model.Prelude
import Tex2lean.Meta.ModelClosure

/-!
# Pseudocode — there is no algorithm, and nothing here is probabilistic

The paper is pure algebra. It contains no algorithm, no computation, no sampling
and no probability: Proposition 2.4 is an ordinary `Prop` over a ring, not a
statement about a distribution, and there is no `PMF` anywhere in this
development. Writing one would be inventing a sample space the paper does not
have. The only thing in the paper that resembles a construction is the
extraction of a Drazin-inverse witness `(y, k)` from a hypothesis and the
assembly of a new one for the conclusion — in claim (ii) the paper's route
produces `y = π(a₁)ᴰ * π(a₂)ᴰ` — and that is witness-building inside a proof,
not a procedure the theorem is about.

So what this file carries is the other half of its job: **the object the
theorem's claims are about**, named once so a referee can see it.

Proposition 2.4 is a closure statement about a single set,

  `BF(A, J) = π⁻¹ {x ∈ A ⧸ J | x is Drazin invertible}`,

and its three claims say that this set is closed under, respectively, addition
of two members that annihilate each other modulo `J`, multiplication of two
members that commute modulo `J`, and perturbation by an element of `J`. No
numerical quantity enters — no index, no dimension, no norm. (The index
`i(a) = τ([a, a₀])` of Definition 3.2 belongs to Section 3 and plays no role in
Section 2.)
-/

namespace Tex2lean.Model

/-- `bFredholm J` is the set of B-Fredholm elements of `A` modulo `J`, i.e. the
preimage under `π : A →+* A ⧸ J` of the Drazin invertible elements of `A ⧸ J`.

This is `BF(A, J)`, the set whose closure properties are the three claims of
Proposition 2.4. -/
def bFredholm {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] : Set A :=
  {a : A | IsBFredholm J a}

#modelClosure bFredholm

end Tex2lean.Model
