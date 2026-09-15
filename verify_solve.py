"""Verify that solution/solve.sh reproduces DrazinCharacterization.lean byte-for-byte."""
import os

REPO = r"C:\Users\Berkani\Documents\GitHub\Tex2Lean"

script = open(os.path.join(REPO, "solution", "solve.sh"), encoding="utf-8").read()
marker = "<< 'LEAN_EOF'\n"
i = script.index(marker) + len(marker)
j = script.index("\nLEAN_EOF", i)
body = script[i:j] + "\n"

ref = open(os.path.join(REPO, "DrazinCharacterization.lean"), encoding="utf-8").read()
print("solve.sh body == reference file:", body == ref)
print("body lines:", body.count("\n"), " ref lines:", ref.count("\n"))

# structural checks on the script itself
print("starts with shebang:", script.startswith("#!/bin/bash\n"))
print("cd line:", script.split("\n")[1])
print("mkdir line:", script.split("\n")[2])
print("no CRLF:", "\r" not in script)
print("no BOM:", not script.startswith("\ufeff"))

# the exact content tests will see
out = os.path.join(REPO, "verify", "Tex2lean", "DrazinCharacterization.lean")
cur = open(out, encoding="utf-8").read()
print("verify workspace copy already validated:", cur == ref)