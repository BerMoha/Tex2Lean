import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel

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


# What this development assumes
The results this proof takes from prior work — cited, standard, or folklore —
stated as the hypotheses they are. `Prior` is a field per borrowed result, and the
theorem carries it as `(hprior : Prior)`, so what was granted is in the statement
rather than hidden somewhere under it.
It is empty because nothing has been surveyed yet. The pass that reads the
paper for what the proof leans on fills it in; until then the theorem assumes
nothing and `hprior` is discharged by `⟨⟩`.
-/
/-- Every result this development takes from prior work rather than proving. -/
structure Prior : Prop where

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

/-!
# Analysis/SpectralIdempotents: the two idempotents of the splitting

The second claim of the paper (`authoring/theorem.tex:10-12`): when `A = cA ⊕ N(c)` there
are idempotents `p, q` with `e = p + q`, `pq = qp = 0` and `A = pA ⊕ qA`.

The paper extracts `p` and `q` from the decomposition of `e` itself.  Here they are built
from the group inverse `d` of `c` supplied by `Analysis/GroupInverse`, as `p = cd` and
`q = e - cd`; that is the same pair — the paper's own argument shows its `p` equals `ab`
(`authoring/theorem.tex:34-36`) — and it makes the two extra equalities
`pA = cA` and `N(c) = qA` immediate, which is what turns the idempotent claim from a
vacuous one (`p = e, q = 0` satisfies the bare conditions) into the paper's.
-/



/-- From a group inverse `d` of `c`, the paper's two idempotents `p = cd` and `q = e - cd`,
together with `pA = cA` and `N(c) = qA`.

PAPER: authoring/theorem.tex:10-12 and 26-36. -/
theorem exists_idempotents_of_groupInverse {c d : A} (hcdc : c * d * c = c)
    (hcd : c * d = d * c) :
    ∃ p q : A,
      IsIdempotentElem p ∧ IsIdempotentElem q ∧
      p + q = 1 ∧ p * q = 0 ∧ q * p = 0 ∧
      IsCompl (rightMul p) (rightMul q) ∧
      rightMul p = rightMul c ∧ rightAnn c = rightMul q := by
  -- `p = cd` is idempotent, `pc = c` and `cp = c`.
  have hp : c * d * (c * d) = c * d := by rw [← mul_assoc, hcdc]
  have hcp : c * (c * d) = c := by rw [hcd, ← mul_assoc, hcdc]
  have hpq : c * d * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have hqp : (1 - c * d) * (c * d) = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have hcq : c * (1 - c * d) = 0 := by rw [mul_sub, mul_one, hcp, sub_self]
  refine ⟨c * d, 1 - c * d, hp, ?_, by abel, hpq, hqp, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- `q` is idempotent
    show (1 - c * d) * (1 - c * d) = 1 - c * d
    rw [mul_sub, mul_one, hqp, sub_zero]
  · -- `pA ⊓ qA = ⊥`
    refine Submodule.disjoint_def.mpr ?_
    rintro x ⟨u, rfl⟩ ⟨v, hv⟩
    have hv' : (1 - c * d) * v = c * d * u := hv
    have h1 : c * d * (c * d * u) = c * d * u := by rw [← mul_assoc, hp]
    have h2 : c * d * (c * d * u) = 0 := by rw [← hv', ← mul_assoc, hpq, zero_mul]
    exact h1.symm.trans h2
  · -- `pA ⊔ qA = ⊤`
    intro s hps hqs x _
    have h1 : c * d * x ∈ s := hps ⟨x, rfl⟩
    have h2 : (1 - c * d) * x ∈ s := hqs ⟨x, rfl⟩
    have hx : c * d * x + (1 - c * d) * x = x := by
      rw [← add_mul]; simp
    exact hx ▸ s.add_mem h1 h2
  · -- `pA = cA`
    refine le_antisymm ?_ ?_
    · rintro x ⟨t, rfl⟩
      exact ⟨d * t, by show c * (d * t) = c * d * t; rw [← mul_assoc]⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨c * t, by show c * d * (c * t) = c * t; rw [← mul_assoc, hcdc]⟩
  · -- `N(c) = qA`
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : c * x = 0 := hx
      refine ⟨x, ?_⟩
      show (1 - c * d) * x = x
      rw [sub_mul, one_mul, hcd, mul_assoc, hx', mul_zero, sub_zero]
    · rintro x ⟨t, rfl⟩
      show c * ((1 - c * d) * t) = 0
      rw [← mul_assoc, hcq, zero_mul]

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · the idempotent pair `cd`, `e - cd` with all six conditions; fully proved
-/

/-!
# Analysis/TheoremProof: assembling the capstone

The paper's theorem (`authoring/theorem.tex:6-13`) makes two claims about an element `a`
of a unital ring `A`:

* the equivalence — `a` is Drazin invertible iff some positive power `a ^ n` splits `A`
  as `a^n A ⊕ N(a^n)`;
* the idempotent consequence — in that case there are idempotents `p`, `q` with
  `e = p + q`, `pq = qp = 0` and `A = pA ⊕ qA`, realized here in the strengthened form
  `pA = (a^n)A` and `qA = N(a^n)`.

Both are routed through the single pivot of the argument, proved in
`Analysis/GroupInverse`: for one fixed element `c`, the splitting `A = cA ⊕ N(c)` is the
same thing as `c` having a group inverse.  `Analysis/DrazinPower` moves that pivot between
`a` and `a ^ n` — which is the paper's "without loss of generality `k = 1`" — and
`Analysis/SpectralIdempotents` reads the idempotents `p = cd`, `q = e - cd` off the group
inverse.

This file carries no ring computation of its own; it only chains those four lemmas into
the conjunction the audit surface states.  The `Prior` hypothesis of the capstone is empty
and is not used.
-/



/-- The two claims of the paper's theorem, packaged as one conjunction: the Drazin
equivalence together with the strengthened spectral idempotent decomposition at every
positive power that splits.

PAPER: authoring/theorem.tex:6-13 -/
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

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · capstone assembled from `Analysis/GroupInverse`,
  `Analysis/DrazinPower` and `Analysis/SpectralIdempotents`; fully proved.  The route
  through `Model/Pseudocode` was abandoned: `Model/Pseudocode` imports
  `Analysis/PseudocodeProof`, which imports `Model/Theorem`, so importing it here is a
  module cycle — and that file derives the Pseudocode statements *from* this capstone.
-/
/-- The capstone theorem: the Drazin invertibility equivalence together with the
strengthened spectral idempotent decomposition.  The (empty) `Prior` assumption is
carried as the first hypothesis, as required by the audit-surface discipline. -/
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
