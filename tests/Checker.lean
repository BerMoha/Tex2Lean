import Tex2lean.Model.Theorem

example {A : Type*} [Ring A] (a : A) :
    (Tex2lean.IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ Tex2lean.DirectSumDecomp (a ^ n)) ∧
    (∀ n : ℕ, 0 < n → Tex2lean.DirectSumDecomp (a ^ n) →
      ∃ p q : A,
        IsIdempotentElem p ∧ IsIdempotentElem q ∧
          p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
          IsCompl (Tex2lean.rightMul p) (Tex2lean.rightMul q) ∧
          Tex2lean.rightMul p = Tex2lean.rightMul (a ^ n) ∧
          Tex2lean.rightAnn (a ^ n) = Tex2lean.rightMul q) :=
  Tex2lean.drazin_characterization ⟨⟩ a
