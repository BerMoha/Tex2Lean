"""Rebuild DrazinCharacterization.lean from the six source modules, verbatim."""
import os
import re

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"
BUNDLE = r"C:\Users\Berkani\Desktop\drazin-theorem"

FILES = [
    ("Model/Prelude", "lean/Tex2lean/Model/Prelude.lean"),
    ("Model/Prior", "lean/Tex2lean/Model/Prior.lean"),
    ("Analysis/GroupInverse", "lean/Tex2lean/Analysis/GroupInverse.lean"),
    ("Analysis/DrazinPower", "lean/Tex2lean/Analysis/DrazinPower.lean"),
    ("Analysis/SpectralIdempotents", "lean/Tex2lean/Analysis/SpectralIdempotents.lean"),
    ("Analysis/TheoremProof", "lean/Tex2lean/Analysis/TheoremProof.lean"),
]

IMPORTS = [
    "Mathlib.Algebra.Group.Opposite",
    "Mathlib.Algebra.Module.Opposite",
    "Mathlib.Algebra.Module.Submodule.Basic",
    "Mathlib.Algebra.Module.Submodule.Lattice",
    "Mathlib.Algebra.Ring.Idempotent",
    "Mathlib.Tactic.Abel",
]

DROP = ("import ", "namespace Tex2lean", "variable {A : Type*} [Ring A]", "end Tex2lean")

HEADER = """{imports}

/-!
# DrazinCharacterization: monolithic formalization

Everything the task asks for, in one module: the vocabulary of the theorem, the
pivot `A = cA \u2295 N(c) \u2194 c is group invertible`, the paper's reduction from a general
Drazin index to the group-invertible case, the complementary spectral idempotents,
and the capstone `drazin_characterization`.

Assembled verbatim from the `Tex2lean` development modules
`Model/Prelude`, `Model/Prior`, `Analysis/GroupInverse`, `Analysis/DrazinPower`,
`Analysis/SpectralIdempotents` and `Analysis/TheoremProof`.
-/

namespace Tex2lean

variable {{A : Type*}} [Ring A]
""".format(imports="\n".join("import " + i for i in IMPORTS))

CAPSTONE = """
/-- The capstone theorem: the Drazin invertibility equivalence together with the
strengthened spectral idempotent decomposition.  The (empty) `Prior` assumption is
carried as the first hypothesis, so what was granted is visible in the statement. -/
theorem drazin_characterization (hprior : Prior) (a : A) :
    (IsDrazinInvertible a \u2194 \u2203 n : \u2115, 0 < n \u2227 DirectSumDecomp (a ^ n)) \u2227
    (\u2200 n : \u2115, 0 < n \u2192 DirectSumDecomp (a ^ n) \u2192
      \u2203 p q : A,
        IsIdempotentElem p \u2227 IsIdempotentElem q \u2227
          p + q = 1 \u2227 p * q = 0 \u2227 q * p = 0 \u2227
          IsCompl (rightMul p) (rightMul q) \u2227
          rightMul p = rightMul (a ^ n) \u2227 rightAnn (a ^ n) = rightMul q) :=
  drazin_characterization_proof a

end Tex2lean
"""

parts = [HEADER]
for label, rel in FILES:
    raw = open(os.path.join(REPO, rel), encoding="utf-8").read().replace("\r\n", "\n")
    kept = []
    for line in raw.split("\n"):
        s = line.strip()
        if any(s == d or (d.endswith(" ") and s.startswith(d)) for d in DROP):
            continue
        kept.append(line)
    body = "\n".join(kept).strip("\n")
    parts.append("-- " + label + "\n\n" + body + "\n")
parts.append(CAPSTONE.lstrip("\n"))

merged = "\n\n".join(parts)
# collapse 3+ blank lines
merged = re.sub(r"\n{3,}", "\n\n", merged)
if not merged.endswith("\n"):
    merged += "\n"

out = os.path.join(REPO, "DrazinCharacterization.lean")
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    fh.write(merged)
print("wrote", out, len(merged), "chars,", merged.count("\n"), "lines")

# verbatim check: every kept body line from each source must appear in merged
merged_lines = merged.split("\n")
ok = True
for label, rel in FILES:
    raw = open(os.path.join(REPO, rel), encoding="utf-8").read().replace("\r\n", "\n")
    for line in raw.split("\n"):
        s = line.strip()
        if any(s == d or (d.endswith(" ") and s.startswith(d)) for d in DROP):
            continue
        if s and s not in [l.strip() for l in merged_lines]:
            print("MISSING from merge:", label, repr(line))
            ok = False
print("verbatim check:", "OK" if ok else "FAILED")