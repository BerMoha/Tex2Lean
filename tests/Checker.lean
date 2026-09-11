import Tex2lean.Model.Theorem

example {A : Type*} [Ring A] (a : A) (h : IsDrazinInvertible a) :
    (∀ x : A, ∃ y ∈ range_a a, ∃ z ∈ kernel_a a, x = y + z) ∧
    (range_a a ∩ kernel_a a = {0}) :=
  bFredholm_prop_2_4 a h
