# Formalization of Drazin Invertibility Characterization

In ring theory, an element $a$ of a unital ring $A$ is said to be **Drazin invertible** if there exist $b \in A$ and $k \in \mathbb{N}$ such that $bab = b$, $ab = ba$, and $a^k b a = a^k$.

Your task is to formalize the following theorem in Lean 4 with Mathlib:

**Theorem.** Let $A$ be a ring with unit $e$, and let $a \in A$. Then $a$ is Drazin invertible in $A$ **if and only if** there exists a positive integer $n$ such that $A = a^n A \oplus N(a^n)$, where $N(a^n) = \{x \in A \mid a^n x = 0\}$. In this case, there exist two idempotents $p, q$ such that $e = p + q$, $pq = qp = 0$, $A = pA \oplus qA$, $pA = a^n A$, and $N(a^n) = qA$.

## What to produce

Write a complete Lean 4 development rooted at `/workspace/authoring/Tex2lean/` that compiles successfully with `lake build` using the project already configured at `/workspace/authoring`. No file may contain `sorry` placeholders.

The development must define the following under the `Tex2lean` namespace, over a variable `{A : Type*} [Ring A]`:

### Definitions (in `Model/Prelude.lean`)

- `rightMul (a : A) : Submodule Aᵐᵒᵖ A` — the right ideal $aA$.
- `rightAnn (a : A) : Submodule Aᵐᵒᵖ A` — the right annihilator $N(a) = \{x \mid ax = 0\}$.
- `DirectSumDecomp (c : A) : Prop` — the elementwise statement that $A = cA \oplus N(c)$.
- `IsDrazinInverse (a b : A) (k : ℕ) : Prop` — $b$ is a Drazin inverse of $a$ of index $\leq k$.
- `IsGroupInverse (a b : A) : Prop` — the $k = 1$ case.
- `IsGroupInvertible (a : A) : Prop` — existence of a group inverse.
- `IsDrazinInvertible (a : A) : Prop` — existence of a Drazin inverse.

### Capstone theorem (in `Model/Theorem.lean`)

- `drazin_characterization (hprior : Prior) (a : A)` proving:
  1. `IsDrazinInvertible a ↔ ∃ n : ℕ, 0 < n ∧ DirectSumDecomp (a ^ n)` — the equivalence.
  2. For every positive $n$ with `DirectSumDecomp (a ^ n)`, there exist idempotents $p, q$ with $p + q = 1$, $pq = qp = 0$, `IsCompl (rightMul p) (rightMul q)`, `rightMul p = rightMul (a ^ n)`, and `rightAnn (a ^ n) = rightMul q`.

The proof may be split across multiple files under `Tex2lean/Analysis/`. You are free to choose the proof architecture.

You have 3600 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
