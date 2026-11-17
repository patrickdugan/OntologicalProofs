#!/usr/bin/env python3
"""Run local checks and optionally compile the Lean suite with the root toolchain.

Default: require Lean and kernel compilation. --python-only explicitly records
Lean as NOT_RUN. A source scan cannot substitute for a kernel check.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
from audit import audit_all  # noqa: E402


def strip_comments(source: str) -> str:
    """Strip nested Lean block comments and line comments for a lexical smoke test."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth or quoted:
        raise ValueError("Unclosed Lean comment or string")
    return "".join(out)


def source_checks() -> dict:
    sources = {}
    names = []
    for path in sorted(HERE.glob("*.lean")):
        source = strip_comments(path.read_text(encoding="utf-8"))
        banned = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", source)
        if banned:
            raise ValueError(f"Forbidden source token in {path.name}: {banned}")
        theorems = re.findall(r"(?m)^theorem\s+(\w+)", source)
        printed = re.findall(r"(?m)^#print axioms\s+(\w+)", source)
        if sorted(theorems) != sorted(printed):
            raise ValueError(f"Every theorem needs a dependency print: {path.name}")
        names.extend("MoralRealism." + n for n in theorems)
        sources[path.name] = len(theorems)
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty or duplicate theorem inventory")
    return {"theorems_per_file": sources, "theorem_names": sorted(names),
            "scope": "lexical smoke check; kernel dependency check is separate"}


def run(command: list[str]) -> str:
    completed = subprocess.run(command, cwd=ROOT, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               check=False, timeout=900)
    print("$ " + " ".join(command), flush=True)
    print(completed.stdout, flush=True)
    if completed.returncode:
        raise RuntimeError(f"Command failed with code {completed.returncode}: {command}")
    return completed.stdout


def compile_lean(expected: list[str]) -> dict:
    if shutil.which("lake") is None:
        raise RuntimeError("lake is unavailable; use --python-only to record partial verification")
    version = run(["lake", "env", "lean", "--version"]).strip()
    run(["lake", "build", "Neoplatonic"])
    output_dir = ROOT / ".lake" / "build" / "lib" / "lean" / "MoralRealism"
    output_dir.mkdir(parents=True, exist_ok=True)
    log = ""
    for name in ("Kernel", "GroundingBridge"):
        log += run(["lake", "env", "lean", "-o", str(output_dir / (name + ".olean")),
                    str(HERE / (name + ".lean"))])
    pattern = r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    dependencies = {}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, raw in re.findall(pattern, log, flags=re.MULTILINE):
        axioms = sorted(x.strip() for x in raw.split(",") if x.strip())
        if set(axioms) - allowed:
            raise ValueError(f"Unapproved theorem dependencies: {name}: {axioms}")
        dependencies[name] = axioms
    if set(dependencies) != set(expected):
        raise ValueError("Kernel dependency output does not match the complete theorem inventory")
    return {"status": "PASS", "version": version, "axioms": dependencies}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python-only", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = {"schema": "moral_realism_verification_v1", "status": "RUNNING",
              "lean": {"status": "NOT_RUN"}}
    try:
        report["source_checks"] = source_checks()
        suite = unittest.defaultTestLoader.discover(str(HERE), pattern="test_*.py")
        stream = io.StringIO()
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
        print(stream.getvalue(), flush=True)
        report["python"] = {"tests_run": result.testsRun, "failures": len(result.failures),
                            "errors": len(result.errors), "skipped": len(result.skipped)}
        if not result.wasSuccessful() or result.skipped:
            raise RuntimeError("Python tests failed or were skipped")
        report["finite_audit"] = audit_all()
        recorded = HERE / "finite_audit.json"
        if recorded.exists() and json.loads(recorded.read_text()) != report["finite_audit"]:
            raise ValueError("Committed finite-audit result differs from the fresh run")
        if args.python_only:
            report["status"] = "PYTHON_PASS_LEAN_NOT_RUN"
        else:
            report["lean"] = {"status": "RUNNING"}
            report["lean"] = compile_lean(report["source_checks"]["theorem_names"])
            report["status"] = "PASS"
    except Exception as exc:
        report["status"] = "FAILED"
        if report["lean"]["status"] == "RUNNING":
            report["lean"] = {"status": "FAILED"}
        report["error"] = f"{type(exc).__name__}: {exc}"
    report["source_sha256"] = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(HERE.iterdir()) if path.suffix in {".lean", ".py", ".md"}}
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    print(text, flush=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as handle:
            handle.write("## MoralRealism verification\n\n```json\n" + text + "```\n")
    return 1 if report["status"] == "FAILED" else 0


if __name__ == "__main__":
    raise SystemExit(main())
