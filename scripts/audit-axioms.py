#!/usr/bin/env python3
"""Check the actual transitive dependencies printed by Lean for release targets.

Run after building the project. This complements the sandboxed Comparator;
it does not replace independent statement comparison or kernel replay.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()
    audit = root / "TranscendentalTuran/Audit.lean"
    expected = re.findall(r"^#print axioms\s+(\S+)\s*$", audit.read_text(), re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise SystemExit("Audit.lean must name a nonempty list of distinct declarations")
    allowed = set(json.loads((root / "comparator.json").read_text())["permitted_axioms"])
    result = subprocess.run(
        [args.lake, "env", "lean", str(audit.relative_to(root))],
        cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    sys.stdout.write(result.stdout)
    if args.log:
        args.log.parent.mkdir(parents=True, exist_ok=True)
        args.log.write_text(result.stdout, encoding="utf-8")
    if result.returncode:
        return result.returncode
    found = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout):
        found[name] = {part.strip() for part in body.split(",") if part.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        found[name] = set()
    missing = set(expected) - found.keys()
    forbidden = {name: sorted(found[name] - allowed) for name in expected
                 if name in found and found[name] - allowed}
    if missing or forbidden:
        print(json.dumps({"missing_audits": sorted(missing), "forbidden_axioms": forbidden},
                         ensure_ascii=False, indent=2), file=sys.stderr)
        return 1
    print(f"PASS: {len(expected)} declarations; all axioms belong to {sorted(allowed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
