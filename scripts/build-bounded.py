#!/usr/bin/env python3
"""Run genuine Lake module builds with a bounded number of active compilers.

This schedules local modules in dependency order. It never edits Lake traces,
skips dependency validation, or supplies compiler artifacts. Every scheduled
module is built by the project's pinned Lake executable in the usual way.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parent.parent


def uncomment(text: str) -> str:
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i + 2] == "/-":
            depth += 1
            i += 2
        elif depth and text[i:i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                result.append("\n")
            i += 1
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def local_modules() -> dict[str, Path]:
    paths = [p for p in ROOT.glob("*.lean") if p.name != "lakefile.lean"]
    for directory in ("TranscendentalTuran", "TuranUniversality"):
        paths.extend((ROOT / directory).rglob("*.lean"))
    return {str(p.relative_to(ROOT).with_suffix("")).replace("/", "."): p for p in paths}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", default=["TranscendentalTuran.Main"])
    parser.add_argument("--all", action="store_true", help="check every local Lean module")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--log-dir", type=Path, default=Path("/tmp/transcendental-turan-build"))
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    modules = local_modules()
    pattern = re.compile(r"(?m)^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+([^\n]+)")
    dependencies = {}
    for name, path in modules.items():
        imports = [word for match in pattern.findall(uncomment(path.read_text())) for word in match.split()]
        dependencies[name] = {x for x in imports if x in modules}
    selected = set(modules) if args.all else set()

    def include(name: str) -> None:
        if name not in modules:
            parser.error(f"unknown local module: {name}")
        if name in selected:
            return
        selected.add(name)
        for dep in dependencies[name]:
            include(dep)

    if not args.all:
        for target in args.targets:
            include(target)
    args.log_dir.mkdir(parents=True, exist_ok=True)
    states = {name: "pending" for name in selected}
    durations = {}
    source_digests = {}
    attempts = {name: 0 for name in selected}
    running = {}

    def digest(name: str) -> str:
        return hashlib.sha256(modules[name].read_bytes()).hexdigest()

    def persist() -> None:
        (args.log_dir / "status.json").write_text(json.dumps({
            "root": str(ROOT), "jobs": args.jobs, "states": states,
            "durations_seconds": durations,
            "source_sha256": source_digests, "attempts": attempts,
        }, indent=2, sort_keys=True) + "\n")

    def build(name: str) -> tuple[int, float]:
        started = time.monotonic()
        with (args.log_dir / (name + ".log")).open("w") as log:
            result = subprocess.run([args.lake, "--fail-fast", "build", "+" + name],
                                    cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        return result.returncode, time.monotonic() - started

    print(f"Checking {len(selected)} local modules with at most {args.jobs} Lake builds", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while True:
            # An agent may repair a failed source while independent modules
            # continue. Retry only after its bytes actually change, and let
            # Lake validate all dependencies again in the usual way.
            repaired = []
            for name, state in states.items():
                if state == "failed" and digest(name) != source_digests.get(name):
                    repaired.append(name)
            if repaired:
                for name in repaired:
                    states[name] = "pending"
                    imports = [word for match in pattern.findall(uncomment(modules[name].read_text()))
                               for word in match.split()]
                    dependencies[name] = {x for x in imports if x in modules}
                    for dep in dependencies[name]:
                        include(dep)
                    print(f"RETRY {name} (source changed after failure)", flush=True)
                for name in selected - states.keys():
                    states[name] = "pending"
                    attempts[name] = 0
                for name, state in states.items():
                    if state == "blocked":
                        states[name] = "pending"
            for name in sorted(selected):
                if states[name] != "pending":
                    continue
                if any(states[dep] in {"failed", "blocked"} for dep in dependencies[name]):
                    states[name] = "blocked"
            ready = [name for name in sorted(selected) if states[name] == "pending"
                     and all(states[dep] == "passed" for dep in dependencies[name])]
            for name in ready[:max(0, args.jobs - len(running))]:
                states[name] = "running"
                source_digests[name] = digest(name)
                old_log = args.log_dir / (name + ".log")
                if attempts[name] and old_log.exists():
                    shutil.copyfile(old_log, args.log_dir / f"{name}.attempt-{attempts[name]}.log")
                attempts[name] += 1
                running[executor.submit(build, name)] = name
                print(f"START {name}", flush=True)
            persist()
            if not running:
                break
            finished, _ = wait(running, timeout=30, return_when=FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                code, elapsed = future.result()
                states[name] = "passed" if code == 0 else "failed"
                durations[name] = round(elapsed, 2)
                print(f"{states[name].upper()} {name} ({elapsed:.1f}s)", flush=True)
            persist()
    # Resolve descendants of failures regardless of alphabetical ordering.
    changed = True
    while changed:
        changed = False
        for name, state in states.items():
            if state == "pending" and any(states[d] in {"failed", "blocked"} for d in dependencies[name]):
                states[name] = "blocked"
                changed = True
    persist()
    totals = {s: sum(v == s for v in states.values()) for s in sorted(set(states.values()))}
    print(json.dumps(totals, sort_keys=True), flush=True)
    return 0 if all(state == "passed" for state in states.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
