"""Sanity checks for the Tex2Lean bundle: BOM, line endings, key content."""
import os
import re

ROOTS = [
    r"C:\Users\Berkani\Documents\GitHub\Tex2Lean",
    r"C:\Users\Berkani\Desktop\drazin-theorem",
]
EXTS = (".sh", ".lean", ".md", ".toml", ".py")
SKIP_DIRS = {".git", ".lake", ".paper", "scratch", "scripts", "node_modules"}


def walk(root):
    for dp, dns, fs in os.walk(root):
        dns[:] = [d for d in dns if d not in SKIP_DIRS]
        for f in fs:
            if f.endswith(EXTS):
                yield os.path.join(dp, f)


for root in ROOTS:
    print("===", root)
    for path in sorted(walk(root)):
        raw = open(path, "rb").read()
        rel = os.path.relpath(path, root)
        notes = []
        if raw.startswith(b"\xef\xbb\xbf"):
            notes.append("BOM")
        if b"\r\n" in raw:
            notes.append("CRLF")
        if rel.endswith(".sh") and not raw.startswith(b"#!/bin/bash"):
            notes.append("BAD-SHEBANG")
        if notes:
            print("  !!", rel, ",".join(notes))
    print("  (scan done)")

# content checks on the monolithic file
mono = open(r"C:\Users\Berkani\Documents\GitHub\Tex2Lean\DrazinCharacterization.lean", encoding="utf-8").read()
print("=== monolithic file")
print("  lines:", mono.count("\n"))
print("  sorry literals:", len(re.findall(r"\bsorry\b", mono)))
print("  decl drazin_characterization:", bool(re.search(r"^theorem drazin_characterization ", mono, re.M)))
print("  decl drazin_characterization_proof:", bool(re.search(r"^theorem drazin_characterization_proof ", mono, re.M)))
print("  namespace:", mono.count("namespace Tex2lean"), " end:", mono.count("end Tex2lean"))
print("  imports:", re.findall(r"^import (\S+)", mono, re.M))
