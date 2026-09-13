#!/bin/bash
cd /workspace/authoring
mkdir -p Tex2lean/Model Tex2lean/Analysis Tex2lean/Meta

cat > Tex2lean/Model/Prior.lean << 'LEAN_EOF'
/-!
# What this development assumes

The results this proof takes from prior work — cited, standard, or folklore —
stated as the hypotheses they are. `Prior` is a field per borrowed result, and the
theorem carries it as `(hprior : Prior)`, so what was granted is in the statement
rather than in a `sorry` somewhere under it.

It is empty because nothing has been surveyed yet. The pass that reads the
paper for what the proof leans on fills it in; until then the theorem assumes
nothing and `hprior` is discharged by `⟨⟩`.
-/

namespace Tex2lean

/-- Every result this development takes from prior work rather than proving. -/
structure Prior : Prop where

end Tex2lean
LEAN_EOF

cat > Tex2lean/Model/Prelude.lean << 'LEAN_EOF'
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
LEAN_EOF

cat > Tex2lean/Analysis/GroupInverse.lean << 'LEAN_EOF'
import Tex2lean.Model.Prelude
import Mathlib.Tactic.Abel

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem mem_rightMul {c x : A} : x ∈ rightMul c ↔ ∃ t, c * t = x := Iff.rfl

theorem mem_rightAnn {c x : A} : x ∈ rightAnn c ↔ c * x = 0 := Iff.rfl

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

theorem groupInverse_of_directSumDecomp {c : A} (h : DirectSumDecomp c) :
    ∃ d : A, c * d * c = c ∧ d * c * d = d ∧ c * d = d * c := by
  obtain ⟨hex, huniq⟩ := h
  obtain ⟨t, q, h1, hcq⟩ := hex 1
  have hq : q = 1 - c * t := by rw [h1]; abel
  have hcp : c * (c * t) = c := by
    have h2 : c * (c * t + q) = c * 1 := by rw [← h1]
    rw [mul_add, hcq, add_zero, mul_one] at h2
    exact h2
  have hqc : q * c = 0 := by
    refine huniq (q * c) ⟨1 - t * c, ?_⟩ ?_
    · rw [hq, sub_mul, one_mul, mul_sub, mul_one, mul_assoc]
    · rw [← mul_assoc, hcq, zero_mul]
  have hpc : c * t * c = c := by
    have h2 : (c * t + q) * c = 1 * c := by rw [← h1]
    rw [add_mul, hqc, add_zero, one_mul] at h2
    exact h2
  obtain ⟨t', z, h2, hcz⟩ := hex t
  refine ⟨c * t', ?_, ?_, ?_⟩ <;>
    (have hpb : c * t = c * (c * t') := by
      calc c * t = c * (c * t' + z) := by rw [← h2]
        _ = c * (c * t') + c * z := by rw [mul_add]
        _ = c * (c * t') := by rw [hcz, add_zero])
  · rw [← hpb]; exact hpc
  · have hqb : q * (c * t') = 0 := by
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
  · have hbc : c * t' * c = c * t := by
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

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/GroupInvertibleIffDirectSumDecomp.lean << 'LEAN_EOF'
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Tex2lean.Model.Prelude

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem groupInvertible_iff_directSumDecomp (c : A) :
    IsGroupInvertible c ↔ DirectSumDecomp c := by
  constructor
  · rintro ⟨b, hb1, hb2, hb3⟩
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
      have step2 : b * (c * (c * t)) = c * t := by
        simp only [← mul_assoc]
        rw [hbcc]
      rw [← step2, hz, mul_zero]
  · rintro ⟨hsum, hint⟩
    obtain ⟨t, w, h1, hcw⟩ := hsum 1
    set e := c * t with he
    have hw : w = 1 - e := by rw [h1]; abel
    have hce : c * e = c := by
      have hcw' : c * (1 - e) = 0 := by rw [← hw]; exact hcw
      rw [mul_sub, mul_one, sub_eq_zero] at hcw'
      exact hcw'.symm
    have hcet : c * c * t = c * e := by rw [he, mul_assoc]
    have hidem : e * e = e := by
      have hu : e - e * e = c * (t * (1 - e)) := by
        rw [he]; noncomm_ring
      have hcu : c * (t * (1 - e)) = 0 := by
        have key : c * (c * (t * (1 - e))) = 0 := by
          rw [← mul_assoc, ← mul_assoc, hcet, hce, mul_sub, mul_one, hce, sub_self]
        exact hint (c * (t * (1 - e))) ⟨t * (1 - e), rfl⟩ key
      have : e - e * e = 0 := by rw [hu, hcu]
      exact sub_eq_zero.mp this |>.symm
    have hec : e * c = c := by
      have hv : e * c - c = c * (t * c - 1) := by
        rw [he]; noncomm_ring
      have hcv : c * (t * c - 1) = 0 := by
        have key : c * (c * (t * c - 1)) = 0 := by
          rw [← mul_assoc, mul_sub, mul_one, ← mul_assoc, hcet, hce, sub_self]
        exact hint (c * (t * c - 1)) ⟨t * c - 1, rfl⟩ key
      have hv0 : e * c - c = 0 := by rw [hv, hcv]
      exact sub_eq_zero.mp hv0
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
    refine ⟨e * t, ?_, ?_, ?_⟩
    · have step : c * (e * t) = e := by rw [← mul_assoc, hce, ← he]
      rw [step, hec]
    · have step : e * t * c = e := hetc
      rw [step, ← mul_assoc, hidem]
    · have step : c * (e * t) = e := by rw [← mul_assoc, hce, ← he]
      rw [step, hetc]

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/DrazinPower.lean << 'LEAN_EOF'
import Tex2lean.Analysis.GroupInverse

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem exists_pow_groupInverse_of_drazinInvertible {a : A} (h : IsDrazinInvertible a) :
    ∃ (n : ℕ) (d : A), 0 < n ∧ a ^ n * d * a ^ n = a ^ n ∧ d * a ^ n * d = d ∧
      a ^ n * d = d * a ^ n := by
  obtain ⟨b, k, hb, hab, hk⟩ := h
  have hC : Commute a b := hab
  have hidem : IsIdempotentElem (a * b) := by
    show a * b * (a * b) = a * b
    rw [mul_assoc, ← mul_assoc b a b, hb]
  have he : a ^ (k + 1) * b ^ (k + 1) = a * b := by
    rw [← hC.mul_pow, hidem.pow_succ_eq]
  have hpow : a ^ (k + 1) * b ^ (k + 1) = b ^ (k + 1) * a ^ (k + 1) :=
    (hC.pow_pow (k + 1) (k + 1)).eq
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

theorem drazinInvertible_of_pow_groupInverse {a d : A} {n : ℕ} (hn : 0 < n)
    (hcdc : a ^ n * d * a ^ n = a ^ n) (hdcd : d * a ^ n * d = d)
    (hcd : a ^ n * d = d * a ^ n) : IsDrazinInvertible a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hda : d * a = a * d :=
    groupInverse_comm hcdc hdcd hcd (Commute.pow_self a (m + 1)).eq
  have hC : Commute d a := hda
  have hdm : d * a ^ m = a ^ m * d := (hC.pow_right m).eq
  have hcm : a ^ (m + 1) * a ^ m = a ^ m * a ^ (m + 1) :=
    (Commute.pow_pow_self a (m + 1) m).eq
  have hba : a ^ m * d * a = a ^ (m + 1) * d := by
    calc a ^ m * d * a = a ^ m * (d * a) := mul_assoc ..
      _ = a ^ m * (a * d) := by rw [hda]
      _ = a ^ m * a * d := (mul_assoc ..).symm
      _ = a ^ (m + 1) * d := by rw [← pow_succ]
  have hab : a * (a ^ m * d) = a ^ (m + 1) * d := by
    rw [← mul_assoc, ← pow_succ' a m]
  have hcdd : a ^ (m + 1) * d * d = d := by rw [hcd, hdcd]
  refine ⟨a ^ m * d, m + 1, ?_, ?_, ?_⟩
  · calc a ^ m * d * a * (a ^ m * d) = a ^ (m + 1) * d * (a ^ m * d) := by rw [hba]
      _ = a ^ (m + 1) * (d * a ^ m) * d := by simp only [mul_assoc]
      _ = a ^ (m + 1) * (a ^ m * d) * d := by rw [hdm]
      _ = a ^ (m + 1) * a ^ m * (d * d) := by simp only [mul_assoc]
      _ = a ^ m * a ^ (m + 1) * (d * d) := by rw [hcm]
      _ = a ^ m * (a ^ (m + 1) * d * d) := by simp only [mul_assoc]
      _ = a ^ m * d := by rw [hcdd]
  · rw [hab, hba]
  · calc a ^ (m + 1) * (a ^ m * d) * a = a ^ (m + 1) * (a ^ m * d * a) := mul_assoc ..
      _ = a ^ (m + 1) * (a ^ (m + 1) * d) := by rw [hba]
      _ = a ^ (m + 1) * (d * a ^ (m + 1)) := by rw [hcd]
      _ = a ^ (m + 1) * d * a ^ (m + 1) := (mul_assoc ..).symm
      _ = a ^ (m + 1) := hcdc

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/SpectralIdempotents.lean << 'LEAN_EOF'
import Tex2lean.Analysis.GroupInverse
import Mathlib.Algebra.Module.Submodule.Lattice

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem exists_idempotents_of_groupInverse {c d : A} (hcdc : c * d * c = c)
    (hcd : c * d = d * c) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  have hp : c * d * (c * d) = c * d := by rw [← mul_assoc, hcdc]
  have hcp : c * (c * d) = c := by rw [hcd, ← mul_assoc, hcdc]
  have hpq : c * d * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have hqp : (1 - c * d) * (c * d) = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hcq : c * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hcp, sub_self]
  refine ⟨c * d, 1 - c * d, hp, ?_, by abel, hpq, hqp, ⟨?_, ?_⟩, ?_, ?_⟩
  · show (1 - c * d) * (1 - c * d) = 1 - c * d
    rw [mul_sub, mul_one, hqp, sub_zero]
  · refine Submodule.disjoint_def.mpr ?_
    rintro x ⟨u, rfl⟩ ⟨v, hv⟩
    have hv' : (1 - c * d) * v = c * d * u := hv
    have h1 : c * d * (c * d * u) = c * d * u := by rw [← mul_assoc, hp]
    have h2 : c * d * (c * d * u) = 0 := by rw [← hv', ← mul_assoc, hpq, zero_mul]
    exact h1.symm.trans h2
  · intro s hps hqs x _
    have h1 : c * d * x ∈ s := hps ⟨x, rfl⟩
    have h2 : (1 - c * d) * x ∈ s := hqs ⟨x, rfl⟩
    have hx : c * d * x + (1 - c * d) * x = x := by
      rw [← add_mul]; simp
    exact hx ▸ s.add_mem h1 h2
  · refine le_antisymm ?_ ?_
    · rintro x ⟨t, rfl⟩
      exact ⟨d * t, by show c * (d * t) = c * d * t; rw [← mul_assoc]⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨c * t, by show c * d * (c * t) = c * t; rw [← mul_assoc, hcdc]⟩
  · refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : c * x = 0 := hx
      refine ⟨x, ?_⟩
      show (1 - c * d) * x = x
      rw [sub_mul, one_mul, hcd, mul_assoc, hx', mul_zero, sub_zero]
    · rintro x ⟨t, rfl⟩
      show c * ((1 - c * d) * t) = 0
      rw [← mul_assoc, hcq, zero_mul]

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/IdempotentsOfGroupInverse.lean << 'LEAN_EOF'
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic.NoncommRing
import Tex2lean.Model.Prelude

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem idempotents_of_groupInverse (c b : A) (hb : IsGroupInverse c b) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  obtain ⟨h1, h2, h3⟩ := hb
  set p := c * b with hp_def
  set q := (1 : A) - p with hq_def
  have hpp : p * p = p := by
    show (c * b) * (c * b) = c * b
    rw [← mul_assoc (c * b) c b, h1]
  have hpc : p * c = c := h1
  have hcomm : c * b = b * c := hp_def.symm.trans h3
  have hcp : c * p = c := by
    show c * (c * b) = c
    rw [hcomm, ← mul_assoc]
    exact h1
  have hqq : q * q = q := by
    have expand : q * q = 1 - p - p + p * p := by
      show (1 - p) * (1 - p) = 1 - p - p + p * p
      noncomm_ring
    rw [expand, hpp]
    show (1 : A) - p - p + p = 1 - p
    noncomm_ring
  have hpq : p + q = 1 := by
    show p + (1 - p) = 1
    noncomm_ring
  have hpq0 : p * q = 0 := by
    have expand : p * q = p - p * p := by
      show p * (1 - p) = p - p * p
      noncomm_ring
    rw [expand, hpp, sub_self]
  have hqp0 : q * p = 0 := by
    have expand : q * p = p - p * p := by
      show (1 - p) * p = p - p * p
      noncomm_ring
    rw [expand, hpp, sub_self]
  have hrm : rightMul p = rightMul c := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      exact ⟨b * t, (mul_assoc c b t).symm⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨c * t, ?_⟩
      show p * (c * t) = c * t
      rw [← mul_assoc, hpc]
  have hra : rightAnn c = rightMul q := by
    apply le_antisymm
    · intro x hx
      have hcx : c * x = 0 := hx
      have hpx : p * x = 0 := by
        have hbcx : p * x = b * (c * x) := by
          show (c * b) * x = b * (c * x)
          rw [hcomm, mul_assoc]
        rw [hbcx, hcx, mul_zero]
      have hxq : x = q * x := by
        show x = (1 - p) * x
        rw [sub_mul, one_mul, hpx, sub_zero]
      exact ⟨x, hxq.symm⟩
    · rintro _ ⟨t, rfl⟩
      have hcq : c * q = 0 := by
        show c * (1 - p) = 0
        rw [mul_sub, mul_one, hcp, sub_self]
      show c * (q * t) = 0
      rw [← mul_assoc, hcq, zero_mul]
  refine ⟨p, q, hpp, hqq, hpq, hpq0, hqp0, ?_, hrm, hra⟩
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨s, rfl⟩ ⟨t, hxt⟩
    have hxt' : q * t = p * s := hxt
    have e1 : p * (p * s) = p * s := by rw [← mul_assoc, hpp]
    have e2 : p * (p * s) = p * (q * t) := by rw [hxt']
    have e3 : p * (q * t) = 0 := by
      have : p * (q * t) = (p * q) * t := (mul_assoc p q t).symm
      rw [this, hpq0, zero_mul]
    rw [e3] at e2
    rw [e2] at e1
    exact e1.symm
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : x = p * x + q * x := by
      have hstep : (p + q) * x = 1 * x := by rw [hpq]
      rw [add_mul, one_mul] at hstep
      exact hstep.symm
    rw [hx]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/IdempotentsOfDirectSumDecomp.lean << 'LEAN_EOF'
import Mathlib.Algebra.Module.Submodule.Lattice
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.GroupInvertibleIffDirectSumDecomp
import Tex2lean.Analysis.IdempotentsOfGroupInverse

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem idempotents_of_directSumDecomp (c : A) (h : DirectSumDecomp c) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  obtain ⟨b, hb⟩ := (groupInvertible_iff_directSumDecomp c).mpr h
  exact idempotents_of_groupInverse c b hb

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/DrazinIffPowGroupInvertible.lean << 'LEAN_EOF'
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.GroupInvertibleIffDirectSumDecomp
import Tex2lean.Analysis.PseudocodeProof

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem drazin_iff_exists_pow_groupInvertible (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ IsGroupInvertible (a ^ n) := by
  rw [drazin_iff_exists_power_decomp' a]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (groupInvertible_iff_directSumDecomp (a ^ n)).2 h⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (groupInvertible_iff_directSumDecomp (a ^ n)).1 h⟩

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/TheoremProof.lean << 'LEAN_EOF'
import Tex2lean.Analysis.DrazinPower
import Tex2lean.Analysis.SpectralIdempotents

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem drazin_characterization_proof (a : A) :
    (IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n)) ∧
    (∀ n : ℕ, 0 < n → DirectSumDecomp (a ^ n) →
      ∃ p q : A,
        IsIdempotentElem p ∧ IsIdempotentElem q ∧
          p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
          IsCompl (rightMul p) (rightMul q) ∧
          rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q) := by
  constructor
  · constructor
    · intro h
      obtain ⟨n, d, hn, hcdc, _, hcd⟩ := exists_pow_groupInverse_of_drazinInvertible h
      exact ⟨n, hn, directSumDecomp_of_groupInverse hcdc hcd⟩
    · rintro ⟨n, hn, hdec⟩
      obtain ⟨d, hcdc, hdcd, hcd⟩ := groupInverse_of_directSumDecomp hdec
      exact drazinInvertible_of_pow_groupInverse hn hcdc hdcd hcd
  · intro n _ hdec
    obtain ⟨d, hcdc, _, hcd⟩ := groupInverse_of_directSumDecomp hdec
    exact exists_idempotents_of_groupInverse hcdc hcd

end Tex2lean
LEAN_EOF

cat > Tex2lean/Analysis/PseudocodeProof.lean << 'LEAN_EOF'
import Tex2lean.Model.Prior
import Tex2lean.Model.Theorem

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem drazin_iff_exists_power_decomp' (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n) :=
  (drazin_characterization ⟨⟩ a).1

theorem exists_spectral_idempotents' (a : A) {n : ℕ} (hn : 0 < n)
    (h : DirectSumDecomp (a ^ n)) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q :=
  (drazin_characterization ⟨⟩ a).2 n hn h

end Tex2lean
LEAN_EOF

cat > Tex2lean/Model/Pseudocode.lean << 'LEAN_EOF'
import Mathlib.Algebra.Module.Submodule.Lattice
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.PseudocodeProof

namespace Tex2lean

variable {A : Type*} [Ring A]

theorem drazin_iff_exists_power_decomp (a : A) :
    IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n) :=
  drazin_iff_exists_power_decomp' a

theorem exists_spectral_idempotents (a : A) {n : ℕ} (hn : 0 < n)
    (h : DirectSumDecomp (a ^ n)) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q :=
  exists_spectral_idempotents' a hn h

end Tex2lean
LEAN_EOF

cat > Tex2lean/Model/Theorem.lean << 'LEAN_EOF'
import Tex2lean.Model.Prior
import Tex2lean.Model.Prelude
import Tex2lean.Analysis.TheoremProof
import Mathlib.Algebra.Module.Submodule.Lattice

namespace Tex2lean

variable {A : Type*} [Ring A]

/-- The capstone theorem: the Drazin invertibility equivalence together with the
strengthened spectral idempotent decomposition. -/
theorem drazin_characterization (hprior : Prior) (a : A) :
    (IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n)) ∧
    (∀ n : ℕ, 0 < n → DirectSumDecomp (a ^ n) →
      ∃ p q : A,
        IsIdempotentElem p ∧ IsIdempotentElem q ∧
          p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
          IsCompl (rightMul p) (rightMul q) ∧
          rightMul p = rightMul (a ^ n) ∧ rightAnn (a ^ n) = rightMul q) :=
  drazin_characterization_proof a

end Tex2lean
LEAN_EOF

cat > Tex2lean/Meta/ModelClosure.lean << 'LEAN_EOF'
import Lean

open Lean Elab Command

namespace Tex2lean.Meta

private partial def closureAux (env : Environment) :
    NameSet → List Name → NameSet → NameSet
  | _, [], acc => acc
  | seen, c :: rest, acc =>
    if seen.contains c then closureAux env seen rest acc
    else
      let seen := seen.insert c
      let acc := if (`Tex2lean).isPrefixOf c then acc.insert c else acc
      match env.find? c with
      | none => closureAux env seen rest acc
      | some ci =>
        let next := ci.type.getUsedConstants.toList
          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])
        closureAux env seen (next ++ rest) acc

private def moduleOf (env : Environment) (c : Name) : Name :=
  match env.getModuleIdxFor? c with
  | some idx => (env.allImportedModuleNames[idx.toNat]?).getD `«unknown»
  | none => env.mainModule

private def outsideModel (env : Environment) (cls : NameSet) : List (Name × Name) :=
  cls.toList.filterMap fun c =>
    let mod := moduleOf env c
    if (`Tex2lean.Model).isPrefixOf mod then none else some (c, mod)

elab "#modelClosure " id:ident : command => do
  let env ← getEnv
  let n ← liftCoreM <| Lean.realizeGlobalConstNoOverload id
  let cls := (closureAux env {} [n] {}).erase n
  match outsideModel env cls with
  | [] => logInfo m!"OK — closure of {n} is defined entirely under Model/ ({cls.toList.length})"
  | bad => throwError m!"OUTSIDE Model/ in closure of {n}: {bad}"

elab "#modelClosureOfType " id:ident : command => do
  let env ← getEnv
  let some ci := env.find? (← liftCoreM <| Lean.realizeGlobalConstNoOverload id)
    | throwError "unknown constant"
  let cls := closureAux env {} ci.type.getUsedConstants.toList {}
  match outsideModel env cls with
  | [] => logInfo m!"OK — the STATEMENT is defined entirely under Model/ ({cls.toList.length})"
  | bad => throwError m!"OUTSIDE Model/ in the statement: {bad}"

end Tex2lean.Meta
LEAN_EOF
