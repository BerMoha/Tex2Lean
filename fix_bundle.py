"""Normalize line endings / BOM and rebuild solution/solve.sh."""
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"
BUNDLE = r"C:\Users\Berkani\Desktop\drazin-theorem"
BOM = b"\xef\xbb\xbf"


def read_lf(path):
    data = open(path, "rb").read().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
    if data.startswith(BOM):
        data = data[len(BOM):]
    return data


def write(path, data):
    with open(path, "wb") as fh:
        fh.write(data)
    print("wrote", os.path.relpath(path, REPO if path.startswith(REPO) else BUNDLE), len(data), "bytes")


mono = read_lf(os.path.join(REPO, "DrazinCharacterization.lean"))

write(os.path.join(REPO, "DrazinCharacterization.lean"), mono)
write(os.path.join(REPO, "lean", "Tex2lean", "DrazinCharacterization.lean"), mono)

solve = (
    "#!/bin/bash\n"
    "cd /workspace/authoring\n"
    "mkdir -p Tex2lean\n"
    "cat > Tex2lean/DrazinCharacterization.lean << 'LEAN_EOF'\n"
    + mono.decode("utf-8")
    + "LEAN_EOF\n"
)
write(os.path.join(REPO, "solution", "solve.sh"), solve.encode("utf-8"))

write(os.path.join(BUNDLE, "solution", "solve.sh"), solve.encode("utf-8"))
write(os.path.join(BUNDLE, "authoring", "Tex2lean", "DrazinCharacterization.lean"), mono)

stray = os.path.join(BUNDLE, "DrazinCharacterization.lean")
if os.path.exists(stray):
    os.remove(stray)
    print("removed stray bundle file DrazinCharacterization.lean")