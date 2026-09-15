"""Inspect namespace / variable / end lines of each source file."""
import re
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"
FILES = [
    "lean/Tex2lean/Model/Prelude.lean",
    "lean/Tex2lean/Model/Prior.lean",
    "lean/Tex2lean/Analysis/GroupInverse.lean",
    "lean/Tex2lean/Analysis/DrazinPower.lean",
    "lean/Tex2lean/Analysis/SpectralIdempotents.lean",
    "lean/Tex2lean/Analysis/TheoremProof.lean",
]

for f in FILES:
    p = os.path.join(REPO, f)
    lines = open(p, encoding="utf-8").read().split("\n")
    print("===", f, f"({len(lines)} lines)")
    for i, line in enumerate(lines):
        s = line.strip()
        if s.startswith("import ") or s.startswith("namespace ") or s.startswith("variable ") \
           or s.startswith("end ") or s.startswith("open ") or s == "section" or s.startswith("set_option"):
            print(f"  {i+1}: {line}")