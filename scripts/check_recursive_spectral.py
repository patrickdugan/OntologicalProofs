"""Compile and audit every named declaration in the recursive spectral modules.

Each audited module uses a single namespace matching its import path. The
generated manifest and complete Lean output are retained as CI artifacts.
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

MODULES = (
    "Neoplatonic.LTR.RecursiveSpectral",
    "Neoplatonic.LTR.ApproximateIntertwining",
    "Neoplatonic.LTR.WalshFourier",
    "Neoplatonic.LTR.TraceDeterminant",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b")
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|instance)\s+(\w+)",
    re.MULTILINE,
)
REPORT = re.compile(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
    re.DOTALL,
)


def declarations(module: str, source: str) -> list[str]:
    # Conservatively reject these tokens even in comments. This avoids treating
    # a source scanner as a Lean parser; the dependency audit is the proof check.
    forbidden = FORBIDDEN.search(source)
    if forbidden:
        line = source.count("\n", 0, forbidden.start()) + 1
        raise ValueError(f"{module}:{line}: prohibited token {forbidden.group()}")
    namespaces = re.findall(r"^namespace\s+(\S+)\s*$", source, re.MULTILINE)
    if namespaces != [module]:
        raise ValueError(f"{module}: expected one namespace matching the module")
    if re.search(r"^\s*(?:private|protected|opaque)\b", source, re.MULTILINE):
        raise ValueError(f"{module}: unsupported declaration form needs an explicit audit")
    if re.search(r"^\s*instance\s*[:(]", source, re.MULTILINE):
        raise ValueError(f"{module}: every instance needs a name for the audit")
    names = [f"{module}.{name}" for name in DECLARATION.findall(source)]
    if not names or len(names) != len(set(names)):
        raise ValueError(f"{module}: empty or duplicate declaration list")
    return names


def audit_output(expected: list[str], output: str) -> list[str]:
    reports = list(REPORT.finditer(output))
    counts = Counter(report.group(1) for report in reports)
    issues = []
    for name in expected:
        if counts[name] != 1:
            issues.append(f"{name}: expected one report, found {counts[name]}")
    for name in counts.keys() - set(expected):
        issues.append(f"unexpected report: {name}")
    for report in reports:
        axioms = {a.strip() for a in (report.group(2) or "").split(",") if a.strip()}
        extra = axioms - ALLOWED
        if extra:
            issues.append(f"{report.group(1)}: non-standard dependencies {sorted(extra)}")
    for line in output.splitlines():
        if re.search(r"\berror\b|\bsorry\b", line, re.IGNORECASE):
            issues.append(line)
    return issues


def main() -> int:
    names = []
    for module in MODULES:
        source = Path(module.replace(".", "/") + ".lean").read_text(encoding="utf-8")
        names.extend(declarations(module, source))
    manifest = Path("recursive-spectral-axioms.lean")
    manifest.write_text(
        "\n".join([*(f"import {module}" for module in MODULES), "",
                   *(f"#print axioms {name}" for name in names), ""]),
        encoding="utf-8",
    )
    run = subprocess.run(
        ["lake", "env", "lean", str(manifest)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    Path("recursive-spectral-axioms.txt").write_text(run.stdout, encoding="utf-8")
    print(run.stdout, end="")
    issues = audit_output(names, run.stdout)
    if run.returncode:
        issues.append(f"Lean exited with status {run.returncode}")
    print(f"{len(names)} declarations audited; {len(issues)} failures")
    for issue in issues:
        print(issue)
    return 1 if issues else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
