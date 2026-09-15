"""Static analysis of the monolithic merge: order, duplicates, tactics."""
import re
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"
ORIG = [
    "lean/Tex2lean/Model/Prelude.lean",
    "lean/Tex2lean/Model/Prior.lean",
    "lean/Tex2lean/Analysis/GroupInverse.lean",
    "lean/Tex2lean/Analysis/DrazinPower.lean",
    "lean/Tex2lean/Analysis/SpectralIdempotents.lean",
    "lean/Tex2lean/Analysis/TheoremProof.lean",
]
MONO = os.path.join(REPO, "DrazinCharacterization.lean")

print("=== original import graph")
for f in ORIG:
    s = open(os.path.join(REPO, f), encoding="utf-8").read()
    self_mod = f.replace("lean/", "").replace("/", ".").replace(".lean", "")
    deps = [m.group(1) for m in re.finditer(r"^import (Tex2lean\S+)", s, re.M)]
    print(f"  {self_mod} -> {deps}")

print("=== declaration order in mono vs merge order")
mono = open(MONO, encoding="utf-8").read()
DECL = re.compile(r"^(?:private |protected |noncomputable |@\[[^\]]*\]\s*)*(?:theorem|lemma|def|abbrev|structure|instance|class|opaque) ([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
names = [m.group(1) for m in DECL.finditer(mono)]
dups = sorted({n for n in names if names.count(n) > 1})
print("  decl count:", len(names))
print("  duplicate decl names:", dups if dups else "none")
print("  names:", names)

print("=== per-original decl names (for cross-check)")
for f in ORIG:
    s = open(os.path.join(REPO, f), encoding="utf-8").read()
    ns = [m.group(1) for m in DECL.finditer(s)]
    print(f"  {f}: {ns}")

print("=== tactics used in mono")
TACT = ["abel", "ring", "noncomm_ring", "ring_nf", "linarith", "omega", "nlinarith",
        "positivity", "simp_all", "aesop", "polyrith", "field_simp", "gcongr", "bound"]
for t in TACT:
    pat = re.compile(r"(?<![A-Za-z_])" + t + r"(?![A-Za-z_])")
    hits = [i + 1 for i, line in enumerate(mono.split("\n")) if pat.search(line)]
    if hits:
        print(f"  {t}: {len(hits)} lines -> {hits[:8]}")