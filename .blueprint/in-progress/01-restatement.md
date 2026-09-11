# Restated

> A working document, written as this pass finished. The blueprint at the end of the run supersedes it.

## The statement

Setting (Section 2 of the paper, stated in its opening line: "Except when it is clearly specified, in all this section A will be a ring with a unit e, J an ideal of A, and pi : A -> A/J will be the canonical projection"). So: let A be an associative ring with unit e, not assumed commutative and not assumed to be an algebra or a Banach algebra; let J be a (two-sided) ideal of A, so that the quotient A/J is again a ring with unit pi(e); let pi : A -> A/J be the canonical ring epimorphism.

Definitions used (all from the paper, restated with quantifiers explicit).
  (D1) An element x of a unital ring R is Drazin invertible if there exist y in R and k in N such that y*x*y = y, x*y = y*x, and x^k*y*x = x^k. (Given x*y = y*x, the last identity is equivalent to the more familiar x^(k+1)*y = x^k.)
  (D2) [Definition 1.2 of the paper, transplanted to rings in Section 2] An element a of A is a B-Fredholm element of A modulo J if pi(a) is Drazin invertible in the quotient ring A/J.
  (D3) [Definition 1.3] An element a of A is a Fredholm element of A modulo J if pi(a) is invertible in A/J. (Not used by the target statement; listed because it is the ambient vocabulary of the section.)

Target result (Proposition 2.4, the first proposition of the paper, on p. of Section 2, unlabelled in the LaTeX source; source lines 234-243 of "P41- B-Fredholm elements in rings and algebras.tex"). Let a1 and a2 be elements of A that are both B-Fredholm elements in A modulo J. Then all three of the following hold.
  (i) If a1*a2 is in J and a2*a1 is in J, then a1 + a2 is a B-Fredholm element in A modulo J.
  (ii) If a1*a2 - a2*a1 is in J, then a1*a2 is a B-Fredholm element in A modulo J.
  (iii) For every j in J, a1 + j is a B-Fredholm element in A modulo J.

Unwinding (D2), the three claims are exactly: (i) if pi(a1)*pi(a2) = 0 and pi(a2)*pi(a1) = 0 in A/J, then pi(a1) + pi(a2) = pi(a1 + a2) is Drazin invertible in A/J; (ii) if pi(a1) and pi(a2) commute in A/J then their product pi(a1*a2) = pi(a1)*pi(a2) is Drazin invertible in A/J; (iii) pi(a1 + j) = pi(a1) is Drazin invertible in A/J, for any j in J.

No topology, no norm, no semi-primeness, no primitivity, no socle and no index enter this proposition: it is a purely ring-theoretic closure statement about the preimage under pi of the set of Drazin invertible elements of A/J. Hypothesis a2 B-Fredholm is used only in claims (i) and (ii); claim (iii) uses only that a1 is B-Fredholm.

The paper's proof: (i) pi(a1)*pi(a2) = pi(a2)*pi(a1) = 0, so by Drazin's corollary [DR, Corollary 1: in an associative ring, if x and y are Drazin invertible and x*y = y*x = 0 then x + y is Drazin invertible, with (x+y)^D = x^D + y^D] the sum pi(a1) + pi(a2) = pi(a1 + a2) is Drazin invertible. (ii) pi(a1*a2) = pi(a1)*pi(a2) = pi(a2)*pi(a1), so, "similarly to [P10, Proposition 2.6]" (a product of two commuting Drazin invertible elements of a unital algebra is Drazin invertible), pi(a1*a2) is Drazin invertible. (iii) pi(a1 + j) = pi(a1), which is Drazin invertible by assumption.

## What it claims

```
One theorem over a unital (possibly non-commutative) ring A and a two-sided ideal J, with two element variables a1 a2 : A and two hypotheses `IsBFredholm J a1`, `IsBFredholm J a2`, asserting a conjunction of three implications — or, better, split into three named lemmas sharing the same variable block, since claim (iii) does not use a2 at all. Recommended split: `bFredholm_add_of_mul_mem` (i), `bFredholm_mul_of_commute_mod` (ii), `bFredholm_add_mem` (iii), with an aggregate `bFredholm_prop_2_4` conjoining them if the audit surface wants one declaration per paper statement.
```

- **always holds** — (i) If a1, a2 are B-Fredholm mod J and a1*a2 ∈ J and a2*a1 ∈ J, then a1 + a2 is B-Fredholm mod J. (Deterministic algebraic implication. Reduces to: pi(a1)*pi(a2) = 0 = pi(a2)*pi(a1) and both Drazin invertible ⟹ sum Drazin invertible, i.e. Drazin's [DR, Corollary 1]. Both annihilation hypotheses are needed; one-sided annihilation is not enough for Drazin's corollary as stated.)
- **always holds** — (ii) If a1, a2 are B-Fredholm mod J and a1*a2 - a2*a1 ∈ J, then a1*a2 is B-Fredholm mod J. (Deterministic. Reduces to: commuting Drazin invertible elements of a unital ring have Drazin invertible product. This is the only claim with real proof content; its standard proof needs the double-commutant property of the Drazin inverse in a ring.)
- **always holds** — (iii) If a1 is B-Fredholm mod J and j ∈ J, then a1 + j is B-Fredholm mod J. (Deterministic and essentially definitional: pi(a1 + j) = pi(a1) + pi(j) = pi(a1). Should be a two-line proof once `Ideal.Quotient.eq_zero_iff_mem` is in play. Hypothesis `IsBFredholm J a2` is not used.)

## The quantity

**IsBFredholm J a  —  equivalently, Drazin invertibility of pi(a) in A/J** — The single property the proposition is about is membership of an element of A in the set BF(A, J) = pi^{-1}({Drazin invertible elements of A/J}). Every claim of the proposition says that BF(A, J) is closed under a particular operation: addition of two of its elements that annihilate each other modulo J (i), multiplication of two of its elements that commute modulo J (ii), and perturbation by an element of J (iii). No numerical quantity (no index, no dimension, no norm) appears; the index i(a) = tau([a, a_0]) of Definition 3.2 belongs to Section 3 and plays no role here.

Cross-check: Mathlib has NO Drazin-invertibility API: there is no module whose name contains `Drazin` (glob over the vendored Mathlib returns nothing) and no occurrence of the string `Drazin` under Mathlib/RingTheory, Mathlib/Analysis or Mathlib/Algebra/Ring. So `IsDrazinInvertible` must be introduced by this blueprint, and the honest cross-checks against existing Mathlib notions are sanity lemmas rather than a reuse: (a) `IsUnit x → IsDrazinInvertible x` (take y = x⁻¹, k = 1); (b) `IsNilpotent x → IsDrazinInvertible x` (take y = 0 and k the nilpotency index — this already shows Drazin invertibility is strictly weaker than invertibility and is the reason B-Fredholm is strictly weaker than Fredholm); (c) `IsIdempotentElem x → IsDrazinInvertible x` (take y = x, k = 1); (d) in a `DivisionRing`, every element is Drazin invertible. Cross-check of the quotient layer against Mathlib is direct: `Ideal.Quotient.mk J` is a `RingHom` and `Ideal.Quotient.eq_zero_iff_mem` gives `x ∈ J ↔ pi x = 0`, which is the only property of J the proof uses. If the executor prefers `TwoSidedIdeal A`, the corresponding names are `TwoSidedIdeal.ringCon`, `RingCon.mk'` and `TwoSidedIdeal.rel_iff`.

## Vocabulary

### A (ambient unital ring)

An associative ring with unit e. Section 2 of the paper is explicit that A is only a ring: no commutativity, no field of scalars, no norm, no completeness, and (despite Definition 1.2 having been originally phrased for semi-prime Banach algebras) no semi-primeness is used anywhere in Section 2. The whole point of working in rings here is to cover L(X)/F_0(X), which is not a Banach algebra.

```lean
variable {A : Type*} [Ring A]
```

### J (the ideal modulo which everything is taken)

An ideal of A. The paper writes only "ideal", but the quotient A/J is formed as a ring and pi is used as a ring homomorphism throughout, so J must be TWO-SIDED. Mathlib's `Ideal A` is by default the left-ideal notion (`Submodule A A`); the two-sidedness must be requested explicitly, either as `[J.IsTwoSided]` or by using `TwoSidedIdeal A`. No further hypothesis on J (not prime, not closed, not the socle, not proper) is used by the target proposition; J = A and J = 0 are both allowed and give degenerate but true instances.

```lean
variable (J : Ideal A) [J.IsTwoSided]   -- or  (J : TwoSidedIdeal A)
```

### pi (canonical projection A -> A/J)

The canonical ring epimorphism onto the quotient ring A/J. Used only through: it is a ring hom (so pi(a1+a2) = pi(a1)+pi(a2), pi(a1*a2) = pi(a1)*pi(a2)), it is surjective, and its kernel is exactly J (so x in J iff pi(x) = 0).

```lean
Ideal.Quotient.mk J : A →+* A ⧸ J
-- kernel fact: Ideal.Quotient.eq_zero_iff_mem : Ideal.Quotient.mk J x = 0 ↔ x ∈ J
-- with TwoSidedIdeal instead: (J : TwoSidedIdeal A).ringCon.mk' : A →+* J.ringCon.Quotient
```

### IsDrazinInvertible (Drazin invertibility in a unital ring)

x in a unital ring R is Drazin invertible iff there exist y in R and k in N with y*x*y = y, x*y = y*x, x^k*y*x = x^k. This is the paper's definition verbatim (Section 2, line 209-211 of the source). Since x*y = y*x, the third clause is equivalent to x^(k+1)*y = x^k, which is the form the paper itself uses in the proof of Theorem 2.6. The witness y is unique when it exists (Drazin 1958) and is called THE Drazin inverse x^D; the index of x is the least admissible k. NOT PRESENT IN MATHLIB (see `quantity.crossCheck`): this predicate has to be introduced by the blueprint.

```lean
/-- `y` is a Drazin inverse of `x` of index at most `k`. -/
structure IsDrazinInvOf {R : Type*} [Ring R] (x y : R) (k : ℕ) : Prop where
  bab  : y * x * y = y
  comm : x * y = y * x
  pow  : x ^ k * y * x = x ^ k

def IsDrazinInvertible {R : Type*} [Ring R] (x : R) : Prop :=
  ∃ (y : R) (k : ℕ), IsDrazinInvOf x y k
```

### IsBFredholm (B-Fredholm element of A modulo J)

a in A is a B-Fredholm element of A modulo J iff pi(a) is Drazin invertible in A/J (Definition 1.2, applied to a unital ring as declared at the start of Section 2). This is the property the whole target proposition is about. Note it is a property of the pair (a, J), and it only depends on a through pi(a) — which is literally claim (iii).

```lean
def IsBFredholm {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] (a : A) : Prop :=
  IsDrazinInvertible (Ideal.Quotient.mk J a)
```

### IsFredholmElt (Fredholm element of A modulo J)

a in A is a Fredholm element of A modulo J iff pi(a) is invertible in A/J (Definition 1.3, after Barnes [BA, Def. 2.1]). Not used in the statement or proof of the target proposition, but it is the surrounding vocabulary (Theorems 2.2, 2.6 and the definition of generalized Fredholm element all use it) and the audit prelude will want it for the neighbouring results.

```lean
def IsFredholmElt {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] (a : A) : Prop :=
  IsUnit (Ideal.Quotient.mk J a)
```

### Regularity (Kordula-Muller)

A non-empty subset R of A such that (1) for every a in A and every integer n >= 1, a in R iff a^n in R; (2) for all mutually commuting a,b,c,d in A with a*c + b*d = e, a*b in R iff (a in R and b in R). Used by Theorems 2.2 and 2.3 (the sets of Fredholm and of B-Fredholm elements are regularities) and by the spectral mapping theorem 2.10. NOT used by the target proposition; recorded here because it is adjacent vocabulary and because a downstream pass will need it. Not in Mathlib.

```lean
structure IsRegularity {A : Type*} [Ring A] (S : Set A) : Prop where
  nonempty : S.Nonempty
  pow_mem_iff : ∀ (a : A) (n : ℕ), 1 ≤ n → (a ∈ S ↔ a ^ n ∈ S)
  mul_mem_iff : ∀ a b c d : A, -- pairwise commuting
      a*b = b*a → a*c = c*a → a*d = d*a → b*c = c*b → b*d = d*b → c*d = d*c →
      a*c + b*d = 1 → (a*b ∈ S ↔ a ∈ S ∧ b ∈ S)
```

### Drazin's additivity lemma [DR, Corollary 1]

External input to claim (i): in any associative ring, if x and y are Drazin invertible and x*y = y*x = 0, then x + y is Drazin invertible (Drazin, Amer. Math. Monthly 65 (1958), Corollary 1). This is a real proof obligation for the executor — it is not in Mathlib and it is not proved in the paper.

```lean
theorem IsDrazinInvertible.add_of_mul_eq_zero {R : Type*} [Ring R] {x y : R}
    (hx : IsDrazinInvertible x) (hy : IsDrazinInvertible y)
    (h1 : x * y = 0) (h2 : y * x = 0) : IsDrazinInvertible (x + y)
```

### Commuting-product lemma [P10, Proposition 2.6]

External input to claim (ii): if x and y are Drazin invertible and x*y = y*x, then x*y is Drazin invertible (Berkani-Sarih, Studia Math. 148 (2001), Prop. 2.6; the paper says "similarly to", i.e. it asserts the ring analogue of a result stated there for unital algebras). The usual proof goes through the double-commutant property of the Drazin inverse (anything commuting with x commutes with x^D), which is itself a non-trivial ring-theoretic lemma and also absent from Mathlib.

```lean
theorem IsDrazinInvertible.mul_of_commute {R : Type*} [Ring R] {x y : R}
    (hx : IsDrazinInvertible x) (hy : IsDrazinInvertible y)
    (h : x * y = y * x) : IsDrazinInvertible (x * y)
-- supporting:
theorem IsDrazinInvOf.commute_of_commute {R : Type*} [Ring R] {x y : R} {k : ℕ} {z : R}
    (h : IsDrazinInvOf x y k) (hz : x * z = z * x) : y * z = z * y
```

## Hypotheses

| Hypothesis | Verdict | Why |
| --- | --- | --- |
| A is an associative ring with a unit e. | required | Drazin invertibility as defined (y*x*y = y, x*y = y*x, x^k*y*x = x^k) does not literally mention the unit, but k is allowed to be 0 in the paper's `k ∈ N` and x^0 = e; more importantly the quotient A/J is used as a unital ring by the cited lemmas and by the rest of the section (Theorem 2.6 uses e explicitly). Keep `[Ring A]`. |
| J is an ideal of A — read as: a two-sided ideal. | required | A/J is used as a ring and pi as a ring homomorphism (pi(a1*a2) = pi(a1)*pi(a2) is the first line of the proof of (ii)). A one-sided ideal does not give a ring quotient. The paper never says "two-sided" but the usage forces it; in Lean this is `[J.IsTwoSided]` or `TwoSidedIdeal A`. |
| a1 is a B-Fredholm element of A modulo J. | required | Used in all three claims. Without it (iii) is false: take A = ℤ, J = 0, a1 = 2, j = 0; 2 is not Drazin invertible in ℤ. |
| a2 is a B-Fredholm element of A modulo J. | required | Genuinely required for (i) and (ii). Note for (i): 'a1 B-Fredholm and a1*a2, a2*a1 ∈ J' does not by itself make a1+a2 B-Fredholm — e.g. A = ℤ × ℤ, J = 0, a1 = (1,0), a2 = (0,2): a1*a2 = a2*a1 = 0, a1 is idempotent hence Drazin invertible, but a1 + a2 = (1,2) is not Drazin invertible in ℤ × ℤ. For claim (iii) alone this hypothesis is UNNECESSARY and should be dropped if (iii) is stated as its own lemma. |
| (i) a1*a2 ∈ J and a2*a1 ∈ J. | required | This is what turns the sum into a sum of two mutually annihilating Drazin invertible elements of A/J. Dropping either half breaks the cited additivity result; dropping both makes the claim false (sum of two Drazin invertible elements need not be Drazin invertible: in ℤ, 1 and 1 are units but 2 is not Drazin invertible). |
| (ii) a1*a2 - a2*a1 ∈ J. | required | Commutation modulo J is exactly what puts pi(a1), pi(a2) in the situation of the commuting-product lemma. Without it the claim is false in general (products of non-commuting Drazin invertible elements need not be Drazin invertible; already for 2x2 matrices over ℤ, or in L(X), invertibility modulo the ideal is not preserved). |
| (iii) j ∈ J. | required | This is the whole content: pi kills j. Nothing weaker works. |
| A is a semi-prime Banach algebra (carried over from Definition 1.2, where B-Fredholm elements were first defined). | unnecessary | The opening line of Section 2 replaces it: A is only a unital ring. Nothing in the statement or the proof of Proposition 2.4 uses semi-primeness, a norm, completeness, or a scalar field. Importing `[NormedRing A]` or a semi-primeness hypothesis into the Lean statement would weaken the theorem for no reason and misrepresent the paper. Semi-primeness first matters in Section 3 (via primitivity and the socle), not here. |
| J is the socle of A / A is primitive. | unnecessary | Section 3 hypotheses. Proposition 2.4 quantifies over an arbitrary two-sided ideal J. |
| Existence of a Drazin index k >= 1 rather than k >= 0 in the definition of Drazin invertibility. | discharge-internally | The paper writes `k ∈ N` in Section 2 but `k ∈ N*` in Theorem 2.6 and its proof. The two readings define the same predicate: k = 0 forces y*x = e (with x^0 = e) which together with x*y = y*x makes x a unit, and units already satisfy the k = 1 clause. So the blueprint should fix `k : ℕ` with `x^k` interpreted with `x^0 = 1`, prove once the normalisation lemma `IsDrazinInvOf x y 0 → IsDrazinInvOf x y 1` (and monotonicity in k), and never revisit the question. |

## What the paper leaves unstated

Lean will force each of these. Where one turns out false rather than merely unstated, that is a finding about the paper.

- WHICH PROPOSITION IS THE TARGET. The extraction points at `...tex:21`, which is the line `\newcommand{\bprop}{\begin{proposition}}` in the preamble — a macro definition, not a proposition — and the "verbatim statement" it captured (`}` / `\newcommand{\eprop}{`) is the preamble text lying between the first literal `\begin{proposition}` and the first literal `\end{proposition}`. The extractor never expanded `\bprop`/`\eprop`, so it carries zero information about which real proposition is meant. I have taken the target to be the FIRST proposition in the document body, source lines 234-243, which by the shared `[section]`-numbered counter is PROPOSITION 2.4 (it is unlabelled in the LaTeX, so it has no `\ref` name). The paper contains exactly one other proposition, Proposition 2.5 (`\label{prop1}`, source lines 267-276): "Let A be a ring with unit e and let a ∈ A. Then a is Drazin invertible in A if and only if there exists a non-null positive integer n such that A = a^n A ⊕ N(a^n), where N(a^n) = {x ∈ A | a^n x = 0}. In this case there exist two idempotents p, q such that e = p + q, pq = qp = 0 and A = pA ⊕ qA." If the intended target is that one instead, the vocabulary block above still covers it except that it additionally needs: the right ideal a^n A, the right annihilator N(a^n) (both `Submodule Aᵐᵒᵖ A`-style objects, or plain `Set A` with `IsCompl`-by-hand), and the internal-direct-sum predicate (`IsCompl` on submodules of A viewed as a right module over itself). Switching target is cheap but it must be a deliberate decision, not a default — flagging rather than guessing silently.
- TWO-SIDEDNESS OF J. The paper says only "J an ideal of A" (source line 191) yet immediately forms the ring A/J and treats pi as a ring homomorphism. In Lean `Ideal A` is `Submodule A A`, i.e. a LEFT ideal, and there is no ring structure on the quotient without `[J.IsTwoSided]`. This must be pinned down before any file is written; the choice between `Ideal A` + `[J.IsTwoSided]` and `TwoSidedIdeal A` propagates into every downstream lemma signature.
- N VERSUS N* IN THE DRAZIN DEFINITION. Section 2 (line 210) says `k ∈ N`; Theorem 2.6's statement and proof (lines 308, 314) say `n ∈ N*` and then the converse half of the same proof says `n ∈ N` again. Harmless for the target (see the `hypotheses` entry), but it must be fixed once and for all in the prelude, because downstream statements like Theorem 2.9 ("there exists n ∈ N* such that a^n is a generalized Fredholm element") become vacuous or trivially true under the wrong reading: with n = 0 allowed, a^0 = e is generalized Fredholm for every a, and Theorem 2.9 would assert every element is B-Fredholm.
- CLAIM (iii) IS STATED UNDER AN UNUSED HYPOTHESIS. The proposition's preamble assumes both a1 and a2 are B-Fredholm, but (iii) mentions only a1 and j. Stating (iii) in Lean with the a2 hypothesis attached is faithful to the printed text but produces a lemma nobody can apply without inventing an a2. Recommendation: state (iii) as its own lemma over a single B-Fredholm element, and if the aggregate "Proposition 2.4" declaration is wanted for the audit surface, derive it. This is a shape decision, not a mathematical one, but it should be recorded so the referee is not surprised by the mismatch.
- THE TWO CITED INPUTS ARE STATED FOR ALGEBRAS, NOT RINGS. Claim (ii) is justified by "Similarly to [P10, Proposition 2.6]", and [P10] (Berkani-Sarih, Studia Math. 148 (2001)) works in a unital ALGEBRA, whereas A/J here is only a unital ring. The paper asserts the transfer without proof ("similarly to"). The usual proof of the commuting-product lemma is purely ring-theoretic, but it routes through the double-commutant property (if x*z = z*x then x^D*z = z*x^D), which is a genuine lemma that must be proved in Lean and is not in Mathlib. Likewise [DR, Corollary 1] is stated by Drazin for associative rings (so it does transfer verbatim), but it too is an unproved external input here. The executor should budget for proving BOTH of these from scratch; they, not Proposition 2.4 itself, are where the work is.
- DEGENERATE IDEALS. Neither J ≠ A nor J ≠ 0 is assumed. If J = A then A/J is the zero ring, every element of A is B-Fredholm, and all three claims are vacuously true; Lean will accept this with no extra hypothesis, but a reader comparing against the paper should know the statement is not implicitly assuming J proper. Similarly A itself may be the zero ring.
- UNIQUENESS OF THE DRAZIN INVERSE IS USED IMPLICITLY DOWNSTREAM, NOT HERE. Definition 3.2 (the index, i(a) = tau([a, a_0])) speaks of "a Drazin inverse a_0 of a modulo the socle" and relies on [P42, Theorem 2.3] for well-definedness. Proposition 2.4 needs only EXISTENCE of a witness, so the blueprint can define `IsDrazinInvertible` as a bare existential and defer uniqueness. If a later pass needs `a^D` as a function, uniqueness (Drazin 1958) becomes a prerequisite; noting it now so the definition is not chosen in a way that has to be rewritten.
- WORDING SLIP IN THE PROOF OF (i). The proof concludes "So a1 + a2 is a B-Fredholm element in A", dropping "modulo J"; B-Fredholmness is only ever defined relative to an ideal. Purely cosmetic, but it is the kind of elision that turns into a missing argument in a Lean signature, so the Lean statement should always carry J explicitly.
