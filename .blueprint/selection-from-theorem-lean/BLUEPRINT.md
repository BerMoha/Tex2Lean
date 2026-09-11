# Formalization blueprint — Selection from Theorem.lean

> Generated 2026-09-11T13:04:50.947Z by DeepSeek API · deepseek-v4-pro from `lean\Tex2lean\Model\Theorem.lean:6` (`\begin{selection}`).
> This is a **plan**, not a proof. Every Lean statement below is a proposal to be checked against the paper line by line before anyone starts proving it.

> [!WARNING]
> Built from a raw editor selection, so no macro definitions, labels, or cross-referenced definitions were gathered. Scanning the project instead gives the model the surrounding definitions and usually a materially better plan.

## What this run produced

| Where | What it holds |
| --- | --- |
| `.blueprint/selection-from-theorem-lean/BLUEPRINT.md` | This file: the whole plan, in reading order. |
| `.blueprint/selection-from-theorem-lean/blueprint.json` | The same plan as data — every pass's output verbatim, including the source excerpt it was built from. |
| — | There are no briefs. This plan is executed **top-down**: agents go at the capstone and state the lemmas they turn out to need, so the work list is whatever still carries `sorry` in `lean/` at the start of each round. |
| `lean/Tex2lean/Model/` | The **audit surface**: 3 files holding everything the headline theorem asserts, and nothing else. |
| `lean/README.md` | How to build the project, and the three checks that decide whether it is actually proved. |

### Read it in this order

1. **[The result, restated](#the-result-restated)** — the same statement in words, with a verdict on each hypothesis and what the paper leaves unsaid. Every later section inherits whatever is wrong here, and a plan for the wrong statement looks exactly like a plan for the right one.

2. **The rest of the audit surface** — `lean/Tex2lean/Model/Prelude.lean`, `lean/Tex2lean/Model/Pseudocode.lean`, `lean/Tex2lean/Model/Theorem.lean`. Everything else in the project is machinery serving these. This is the part a reader has to trust, so it is the part to read.

3. **[The crux](#the-crux)** — the 2 steps the proof actually turns on. If the architecture is wrong, it is wrong here, and it is cheaper to find that out before anything else is built.

4. **[Landing order](#landing-order)** — the sequence to prove things in, with what depends on what. Rebuild green after each one.

Sections between the restatement and the crux — the architecture and the reuse map — say what is being taken from Mathlib and arlib rather than proved here, and why the proof is split the way it is. Read them when a decision looks wrong, not before.

## The result, restated

In a unital associative ring A, for every a ∈ A, a is Drazin invertible (there exist b ∈ A and k ∈ ℕ such that bab = b, ab = ba, and a^k b a = a^k) if and only if A decomposes as the direct sum of the left ideal aA = {a x | x ∈ A} and the right annihilator N(a) = {x ∈ A | a x = 0}. Equivalently, every x ∈ A can be written uniquely as x = a t + q with a q = 0. The paper claims this equivalence and proves it by arguing that one may assume k = 1; however that step is false in a general ring, so the formalizable statement must either replace Drazin invertibility by group invertibility (index 1) or add extra hypotheses under which the index can be reduced to 1.

### Claims in the headline

| Claim | Can it fail? | Note |
| --- | --- | --- |
| Forward: if a is Drazin invertible, then A decomposes as aA ⊕ N(a). | no — holds on every reachable outcome | Pure algebraic implication, deterministic. However the paper's proof uses the false assumption that one may take k=1, so this claim as stated for arbitrary Drazin index is not provable; it requires either a corrected definition or additional hypotheses. |
| Converse: if A decomposes as aA ⊕ N(a), then a is Drazin invertible (indeed group invertible with index 1). | no — holds on every reachable outcome | Pure algebraic implication, deterministic. The converse proof constructs b such that aba=a, bab=b, ab=ba, so it proves group invertibility. |

Proposed shape, as the restatement pass wrote it:

```lean
theorem drazin_iff_leftIdeal_directSum (a : A) :
  IsDrazinInvertible a ↔ leftIdeal a ⊔ rightAnnihilator a = ⊤ ∧ leftIdeal a ⊓ rightAnnihilator a = ⊥
```

### Hypotheses

| Hypothesis | Verdict | Why |
| --- | --- | --- |
| A is a unital associative ring | `required` | The proof uses the multiplicative identity e, addition, subtraction, and ring axioms. No commutativity is assumed. |
| a ∈ A | `required` | The element under consideration; no further conditions on a beyond the relevant antecedent. |
| IsDrazinInvertible a (for the forward implication) | `required` | This is the premise of one direction of the iff. |
| A = aA ⊕ N(a) (for the converse implication) | `required` | This is the premise of the other direction. |

### What the paper leaves unstated

Lean will force each of these. Where one turns out to be false rather than
merely unstated, that is a finding about the paper, not a modelling problem.

- The paper says 'without loss of generality, we can assume k=1' from the existence of a Drazin inverse with arbitrary index k. This is false in a general ring: a nilpotent matrix is Drazin invertible (with b=0 and k the nilpotency index) but does not have a group inverse, and A ≠ aA ⊕ N(a). To formalize, either define IsDrazinInvertible to require index 1 (i.e., group invertible) or state the theorem for the subclass where the Drazin index equals 1.
- N(a) is not explicitly defined in the selection. From its use in the proof (a(x-at)=0 implies x-at ∈ N(a); q∈N(a) used to show aq=0 and later qa=0), N(a) is the right annihilator {x | a*x=0}. The proof later derives that elements of N(a) are also right annihilated by a, so the two-sided nature follows from the decomposition.
- The direct sum notation A = aA ⊕ N(a) must be formalized as additive subgroups: leftIdeal a is an additive subgroup (a left ideal) and rightAnnihilator a is an additive subgroup (a right ideal). The decomposition means their sum is all of A and their intersection is zero.
- The step 'there exist r ∈ A such that a=pr' is under-justified in the paper. It likely uses that A = pA ⊕ qA and a = e a = p a + q a; then needs q a = 0 to identify a with p a. But q a = 0 is derived later from aq = qa = 0. The proof order needs formalization care, perhaps by first proving a = p a + q a and then using the direct sum uniqueness to show q a = 0.
- The proof uses p^2 = p, q^2 = q, pq = qp = 0. These are derived from p-p^2 ∈ aA ∩ N(a) and similar considerations, but the details depend on whether N(a) is left or right annihilator. Need to pin down decidability of inclusion in these additive subgroups; no positivity or division issues arise.

## Architecture

The hard mathematics is proved once over a structure of hypotheses; a single
concrete instance then discharges every field. This quarantines the deep
argument from the fiddly modelling, and lets the two halves progress
independently.

### 1. Interface — `CommutingDrazinPair`

| Field | Statement | Why the proof needs it |
| --- | --- | --- |
| `x` | x : R | The first element participating in the commuting product whose Drazin invertibility is assumed. |
| `y` | y : R | The second element participating in the commuting product whose Drazin invertibility is assumed. |
| `hx` | IsDrazinInvertible x | Hypothesis needed to construct a Drazin inverse of the product. |
| `hy` | IsDrazinInvertible y | Hypothesis needed to construct a Drazin inverse of the product. |
| `hcomm` | Commute x y | The multiplicative closure theorem only holds for commuting elements; this is the condition that makes the product well-behaved. |

### 2. Abstract theorem — `drazin_invertible_mul_of_commute`

```lean
∀ {R : Type*} [Ring R] (P : CommutingDrazinPair R), IsDrazinInvertible (P.x * P.y)
```

This is the abstract multiplicative closure of Drazin invertible elements in an arbitrary unital ring. Once proved, it lifts to the quotient A ⧸ J to give closure of bFredholm under multiplication of commuting representatives.

### 3. Concrete discharge — `QuotientCommutingDrazinPair`

- `R` — Take R = A ⧸ J, the quotient ring, which has a Ring instance because J is two-sided.
- `x` — Take x = Ideal.Quotient.mk J a₁, the image of a₁ under the canonical projection.
- `y` — Take y = Ideal.Quotient.mk J a₂, the image of a₂ under the canonical projection.
- `hx` — Unfold IsBFredholm J a₁ to get IsDrazinInvertible (Ideal.Quotient.mk J a₁), and use it directly.
- `hy` — Unfold IsBFredholm J a₂ to get IsDrazinInvertible (Ideal.Quotient.mk J a₂), and use it directly.
- `hcomm` — Use the hypothesis Commute (Ideal.Quotient.mk J a₁) (Ideal.Quotient.mk J a₂) from the bFredholm closure statement, or derive it from the given commutativity of the original elements modulo J.

### 4. Capstone — `bFredholm_prop_2_4`

```lean
∀ {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided], (∀ {a₁ a₂ : A}, IsBFredholm J a₁ → IsBFredholm J a₂ → Ideal.Quotient.mk J a₁ * Ideal.Quotient.mk J a₂ = 0 → Ideal.Quotient.mk J a₂ * Ideal.Quotient.mk J a₁ = 0 → IsBFredholm J (a₁ + a₂)) ∧ (∀ {a₁ a₂ : A}, IsBFredholm J a₁ → IsBFredholm J a₂ → Commute (Ideal.Quotient.mk J a₁) (Ideal.Quotient.mk J a₂) → IsBFredholm J (a₁ * a₂)) ∧ (∀ {a j : A}, IsBFredholm J a → j ∈ J → IsBFredholm J (a + j))
```

## The crux

Prove this first, in isolation. Once it is green the surrounding theorem
usually collapses into bookkeeping — and if it does not, the crux was
mis-identified and the architecture above needs another look.

### `drazin_invertible_mul_of_commute`

```lean
∀ {R : Type*} [Ring R] {x y : R}, IsDrazinInvertible x → IsDrazinInvertible y → Commute x y → IsDrazinInvertible (x * y)
```

**Why this is the heart:** The multiplicative closure is the most delicate part of Proposition 2.4: one must take Drazin inverses of x and y and assemble a Drazin inverse for x*y while preserving the commutation relations. The paper's argument relies on a false WLOG k=1 step, so a correct proof must be constructed directly. Once this lemma is proved, the bFredholm multiplication claim is a straightforward lift through the quotient map.

**How to attack it:** Take Drazin witnesses (u,k) for x and (v,l) for y. Show that u and v commute, or at least that v*u satisfies the Drazin equations for x*y. Use the fact that elements commuting with a strongly π-regular element also commute with its Drazin inverse, or prove the needed commutation from the defining equations hx, hy, and hcomm. Then check the three IsDrazinInvOf fields for x*y with candidate v*u and index max(k,l) (or k+l) by rewriting with associativity, comm, and the existing equations.

### `drazin_invertible_add_of_annihilate`

```lean
∀ {R : Type*} [Ring R] {x y : R}, IsDrazinInvertible x → IsDrazinInvertible y → x * y = 0 → y * x = 0 → IsDrazinInvertible (x + y)
```

**Why this is the heart:** The additive closure under mutual annihilators is the second nontrivial algebraic fact. It is independent of the multiplicative one and can be attacked in parallel. The candidate inverse u+v works, but one must first show that the Drazin inverses u and v annihilate the opposite elements in all necessary ways, which follows from the zero-product hypotheses and the Drazin equations.

**How to attack it:** Take Drazin witnesses (u,k) for x and (v,l) for y. Prove u*y = 0, v*x = 0, and u*v = 0 = v*u from the annihilation hypotheses. Then verify the three IsDrazinInvOf fields for x+y with candidate u+v and index max(k,l), using distributivity and the derived annihilations.

## Invariants to bake into the model

Cheaper as structure fields than as case splits later: Lean's `x / 0 = 0`
convention means a cancellation that ignores the zero case gets stuck on a
false-looking identity.

- `quotient_ring_structure`: For J : Ideal A with [J.IsTwoSided], the quotient A ⧸ J has a Ring instance. — Needed for the Drazin closure lemmas to be applied in the quotient ring.
- `quotient_map_is_ring_hom`: Ideal.Quotient.mk J : A →+* A ⧸ J is a ring homomorphism, so it preserves addition and multiplication. — Used to lift the Drazin closure results from the quotient ring back to representatives in A.
- `perturbation_by_J`: For j ∈ J, Ideal.Quotient.mk J (a + j) = Ideal.Quotient.mk J a. — The perturbation claim of Proposition 2.4 reduces to equality in the quotient; no positivity or division issues arise.

## Modelling decisions

### Prove the closure of bFredholm directly by constructing Drazin inverses for sums and products, instead of following the paper's intermediate lemma A = aA ⊕ N(a).

- **Rejected:** Formalize the paper's proof of the direct-sum lemma and lift it to Drazin invertible elements with arbitrary index.
- **Because:** The paper's WLOG k=1 step is false in a general ring (nilpotent elements are Drazin invertible with index >1 but do not satisfy A = aA ⊕ N(a)). A direct construction avoids this false step and still yields the three closure claims of Proposition 2.4.
- **Scope caveat:** We formalize the closure properties of BF(A,J) as stated in Proposition 2.4. We do not formalize the intermediate direct-sum lemma as it appears in the paper because it is false for general Drazin index. The main result is unaffected.

### Use the project's existing IsDrazinInvertible definition with arbitrary index k : ℕ and do not alter the Model surface.

- **Rejected:** Introduce a separate GroupInvertible predicate or add an extra hypothesis forcing k = 1.
- **Because:** The Model surface is fixed and the true Proposition 2.4 closure holds for arbitrary Drazin index. Changing the definition would create a different theorem, not the one already stated.
- **Scope caveat:** The direct construction avoids any reliance on reducing to index 1, so no extra hypothesis is needed.

### Formulate the additive closure condition as mutual annihilation: both products π(a₁)π(a₂) and π(a₂)π(a₁) equal zero in the quotient.

- **Rejected:** Assume only one product is zero.
- **Because:** The phrase 'annihilate each other' is naturally two-sided, and the sum-of-Drazin-inverses construction requires both directions to verify the Drazin equations.
- **Scope caveat:** If the paper intends only one-sided annihilation, the formal statement will be slightly stronger, which is acceptable.

## Landing order

| # | Lemma | File | Difficulty | Depends on |
| --- | --- | --- | --- | --- |
| 1 | `drazin_invertible_mul_of_commute` | `Analysis/DrazinInvertibleMulOfCommute.lean` | hard | — |
| 2 | `drazin_invertible_add_of_annihilate` | `Analysis/DrazinInvertibleAddOfAnnihilate.lean` | hard | — |
| 3 | `bFredholm_closed_perturb` | `Analysis/BFredholmClosedPerturb.lean` | routine | — |
| 4 | `bFredholm_closed_mul` | `Analysis/BFredholmClosedMul.lean` | moderate | — |
| 5 | `bFredholm_closed_add` | `Analysis/BFredholmClosedAdd.lean` | moderate | — |
| 6 | `bFredholm_prop_2_4` | `Analysis/BFredholmProp24.lean` | routine | `drazin_invertible_mul_of_commute`, `drazin_invertible_add_of_annihilate`, `bFredholm_closed_mul`, `bFredholm_closed_add`, `bFredholm_closed_perturb` |

Rebuild green after each one. Do not batch.

## Files

| Path | Role | Purpose |
| --- | --- | --- |
| `Tex2lean/Model/Prelude.lean` | audit-surface | The vocabulary, and the quantity the theorem is about |
| `Tex2lean/Model/Pseudocode.lean` | audit-surface | The algorithm, transcribed from the paper |
| `Tex2lean/Model/Theorem.lean` | audit-surface | The one theorem this development is for |

## Definition of done

- [ ] The mechanical checks pass. They are run by the extension over the whole project between rounds — the build, the `sorry` warnings, the axiom profile of every headline, a sweep for escape hatches, the closure checks, and the two layout rules — and what they find comes back to you as the next round's brief. Build the modules you created and read their errors; do not try to run the gate.
- [ ] `#print axioms` on the capstone reports exactly the three ambient axioms — propext, Classical.choice, Quot.sound — and nothing else.
- [ ] No `declaration uses sorry` warning anywhere in the build output.
- [ ] A grep sweep for `sorry`, `admit`, `native_decide` and `axiom` over the project comes back clean, and agrees with the other two checks.
- [ ] The closure checks have been observed to *fail* on a deliberately broken control, so that their passing means something.
- [ ] The audit surface still states the paper's theorem: every claim the paper makes is in it, and nothing was weakened to make a proof go through. No script decides this one — the extension's handoff check reads the paper and the surface side by side, and it runs as the last step of a run.

## Risks

- **A round closes the capstone by leaning on lemmas that are themselves still `sorry`, which looks like progress and is not.** — The open-goal list is read out of the Lean sources every round, so a lemma left `sorry` stays on it however the declaration above it was closed.
- **An agent weakens an intermediate lemma until it is provable but useless.** — Whatever depends on it stops building, and the next round re-reads the sources rather than the plan.

## Briefs


---

### Source material this was built from

- Target: `lean\Tex2lean\Model\Theorem.lean:6`
- Files read: `lean\Tex2lean\Model\Theorem.lean`
