# Formalization of Drazin Invertibility

## Difficulty

The problem requires defining a custom Drazin invertibility structure with index k=1 and proving a structured direct sum decomposition of a ring in Lean 4 with Mathlib. This demands exact manipulation of non-commutative ring axioms: the agent must derive intermediate identities like a(ab) = a from the commutativity and aba conditions, construct explicit decomposition witnesses, and prove both the spanning property and the trivial intersection of range and kernel. The non-commutative setting rules out the ring tactic for multiplicative goals, forcing manual rewriting chains that interleave associativity, commutativity, and the Drazin axioms. An expert in interactive theorem proving takes several hours due to the tight coupling between algebraic manipulation and Lean's tactic system.

## Reference solution

The reference solution defines an IsDrazinInvertible structure with three fields (bab, comm, aba), introduces range and kernel as Set A predicates, and proves the decomposition in two parts. Part 1 decomposes any x as abx + (x - abx): the range membership follows from associativity, and the kernel membership uses the key identity a(ab) = a derived from commutativity and the aba axiom. Part 2 shows the intersection is trivial: given x = at with a(at) = 0, the chain at = (aba)t = (ab)(at) = (ba)(at) = 0 uses associativity, commutativity, and the kernel hypothesis.

## Verification

Verification runs lake build on the module Tex2lean.Model.Theorem to guarantee that Lean 4 fully compiles and validates the formal proof. A separate checker module type-checks the theorem signature against the exact required statement, ensuring the file exports the correct definitions with the specified types. Lean's kernel acts as the ground truth: a compiled file has every proof term checked for logical correctness. The verifier additionally rejects files containing sorry placeholders.
