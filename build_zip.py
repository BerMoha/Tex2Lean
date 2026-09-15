"""Build the submission zip from the bundle directory."""
import os
import zipfile

ROOT = r"C:\Users\Berkani\Desktop\drazin-theorem"
OUT = ROOT + ".zip"

if os.path.exists(OUT):
    os.remove(OUT)

names = []
with zipfile.ZipFile(OUT, "w", zipfile.ZIP_DEFLATED) as z:
    for dp, dns, fs in os.walk(ROOT):
        dns[:] = [d for d in dns if d != "__pycache__"]
        for f in sorted(fs):
            if f.endswith(".zip"):
                continue
            full = os.path.join(dp, f)
            arc = os.path.relpath(full, ROOT).replace("\\", "/")
            data = open(full, "rb").read()
            if f.endswith((".sh", ".lean", ".py", ".md", ".toml")):
                assert not data.startswith(b"\xef\xbb\xbf"), f"BOM in {arc}"
                assert b"\r\n" not in data, f"CRLF in {arc}"
            z.writestr(arc, data)
            names.append(arc)

print("ZIP:", os.path.getsize(OUT), "bytes,", len(names), "entries")
for n in sorted(names):
    print("  ", n)

# verify round-trip
with zipfile.ZipFile(OUT) as z:
    bad = z.testzip()
    print("corrupt entry:", bad)
    sh = z.read("solution/solve.sh")
    print("solve.sh first line:", sh.split(b"\n")[0])
    lean = z.read("authoring/Tex2lean/DrazinCharacterization.lean")
    print("lean has capstone:", b"theorem drazin_characterization " in lean)
    print("lean has no sorry:", b"sorry" not in lean)
