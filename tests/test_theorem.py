import subprocess
import os
import re

THEOREM_PATH = "/workspace/authoring/Tex2lean/DrazinCharacterization.lean"


def test_file_exists():
    """The submitted Lean file must exist."""
    assert os.path.exists(THEOREM_PATH), "Theorem.lean was not produced"


def test_no_sorry():
    """No file in the development may contain sorry placeholders."""
    lean_dir = "/workspace/authoring/Tex2lean"
    for root, _, files in os.walk(lean_dir):
        for f in files:
            if f.endswith(".lean"):
                path = os.path.join(root, f)
                with open(path) as fh:
                    content = fh.read()
                assert not re.search(r'\bsorry\b', content), f"{path} contains sorry"


def test_lean_compiles():
    """The full project must compile with lake build."""
    result = subprocess.run(
        ["lake", "build"],
        cwd="/workspace/authoring",
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert result.returncode == 0, f"lake build failed:\n{result.stderr}\n{result.stdout}"


def test_theorem_signature():
    """The capstone theorem must match the required mathematical statement."""
    result = subprocess.run(
        ["lake", "build", "Tex2lean.Checker"],
        cwd="/workspace/authoring",
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert result.returncode == 0, (
        f"Signature check failed — definitions do not match the required types:\n"
        f"{result.stderr}\n{result.stdout}"
    )
