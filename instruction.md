# Formalization of Drazin Invertibility (Proposition 2.4)

In ring theory, an element $a$ of a unital ring $A$ is said to be Drazin invertible (with index $k = 1$) if there exists an element $b \in A$ satisfying $bab = b$, $ab = ba$, and $aba = a$.

Your task is to formalize the following classical result in Lean 4 with Mathlib:

**Proposition.** If $a$ is Drazin invertible in $A$ (with $k = 1$), then $A = aA \oplus \ker(a)$. That is, every element of $A$ decomposes as a sum of an element in the range $aA = \{at \mid t \in A\}$ and an element in the kernel $\ker(a) = \{x \in A \mid ax = 0\}$, and this decomposition is unique (the intersection $aA \cap \ker(a)$ is trivial).

Write a complete Lean 4 file at `/workspace/authoring/Tex2lean/Model/Theorem.lean` that compiles successfully with `lake build Tex2lean.Model.Theorem` using the project already configured at `/workspace/authoring`. The file must contain no `sorry` placeholders.

Your file must define the following names in the root namespace (outside any `namespace` block), over a variable `{A : Type*} [Ring A]`:

- A structure `IsDrazinInvertible (a : A)` with fields `b : A`, `bab : b * a * b = b`, `comm : a * b = b * a`, `aba : a * b * a = a`.
- A definition `range_a (a : A) : Set A` equal to `{ x | ∃ t, x = a * t }`.
- A definition `kernel_a (a : A) : Set A` equal to `{ x | a * x = 0 }`.
- A theorem `bFredholm_prop_2_4` proving that given `(a : A)` and `(h : IsDrazinInvertible a)`, we have `(∀ x : A, ∃ y ∈ range_a a, ∃ z ∈ kernel_a a, x = y + z) ∧ (range_a a ∩ kernel_a a = {0})`.

You have 3600 seconds to complete this task. Do not cheat by using online solutions or hints specific to this task.
