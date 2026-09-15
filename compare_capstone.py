"""Compare the capstone statement in the mono file with Model/Theorem.lean."""
import re
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"


def grab(path, name):
    s = open(path, encoding="utf-8").read()
    m = re.search(r"^theorem " + name + r"\b(.*?):=\s*(?:by|drazin_characterization_proof)", s, re.M | re.S)
    if not m:
        # no body on the := line
        m = re.search(r"^theorem " + name + r"\b(.*?):=", s, re.M | re.S)
    return m.group(1) if m else None


def norm(t):
    return re.sub(r"\s+", "", t) if t else t


a = grab(os.path.join(REPO, "DrazinCharacterization.lean"), "drazin_characterization")
b = grab(os.path.join(REPO, "lean/Tex2lean/Model/Theorem.lean"), "drazin_characterization")
na, nb = norm(a), norm(b)
print("mono statement == original statement:", na == nb)
if na != nb:
    print("MONO:", a)
    print("ORIG:", b)

print()
print("=== 'ring' occurrences with context in mono")
mono = open(os.path.join(REPO, "DrazinCharacterization.lean"), encoding="utf-8").read().split("\n")
for i, line in enumerate(mono):
    if re.search(r"(?<![A-Za-z_])ring(?![A-Za-z_])", line) and "Ring" not in line:
        print(f"  {i+1}: {line.strip()[:110]}")

print()
print("=== mono import block")
for line in mono[:8]:
    print("  ", line)