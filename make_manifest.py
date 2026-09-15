"""Build a lake-manifest.json for the verify workspace (mathlib only, no arlib)."""
import json
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"
src = json.load(open(os.path.join(REPO, "lean", "lake-manifest.json"), encoding="utf-8"))
pkgs = [p for p in src["packages"] if p["name"] != "arlib"]
src["packages"] = pkgs
src["name"] = "tex2lean"
out = os.path.join(REPO, "verify", "lake-manifest.json")
with open(out, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(src, fh, indent=2)
    fh.write("\n")
print("wrote", out)
print("packages:", [(p["name"], p["rev"][:8], p.get("inherited")) for p in pkgs])
