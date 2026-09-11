import subprocess
import os
import re

THEOREM_PATH = "/workspace/authoring/Tex2lean/Model/Theorem.lean"


def test_file_exists():
    """The submitted Lean file must exist."""
    assert os.path.exists(THEOREM_PATH), "Theorem.lean was not produced"


def test_no_sorry():
    """The submitted file must not contain sorry placeholders."""
    with open(THEOREM_PATH) as f:
        content = f.read()
    assert not re.search(r'\bsorry\b', content), "File contains sorry placeholder"


def test_lean_compiles():
    """The submitted file must compile with lake build."""
    result = subprocess.run(
        ["lake", "build", "Tex2lean.Model.Theorem"],
        cwd="/workspace/authoring",
        capture_output=True,
        text=True,
        timeout=600,
    )
    assert result.returncode == 0, f"lake build failed:\n{result.stderr}\n{result.stdout}"


def test_theorem_signature():
    """The theorem must match the required mathematical statement."""
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
