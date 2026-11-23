#!/usr/bin/env python3
"""Replay Palomar's selected con-ron with its positive/ill-typed controls.

Formalization author and responsible maintainer: Xizhi Liu.
This is a local replay, not the public Palomar full-preflight workflow.
The official pinned classifier distinguishes acceptance from an advisory
decline; unknown errors and rejection always fail this driver.
"""

from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time


VERIFIER_COMMIT = "14aa8d6b3c2f14a8540605e37144560b9a00e7e7"
SOURCE_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
LEAN_COMMIT = "11acb17ec6b07a8f9e9173e6845197929540936b"
PINNED_BLOBS = {
    "checker-revisions.json": "ffa97983f87289e48f1e89c99a0c298a730b0829",
    "scripts/verify_submission.py": "35afd78fbc4ba9ecd43a617f99ab8f9a4f376842",
    "scripts/kernel_outcomes.py": "9da438edc0da6f58e667182ecc95791e6d2fa53a",
    "scripts/verification_errors.py": "b4665f25e2492d5ce86a3955e208211043e84c92",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(4 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--export", dest="export_path", type=Path, required=True)
    parser.add_argument("--export-sha256", required=True)
    parser.add_argument("--sandbox", type=Path, default=Path("/usr/bin/bwrap"))
    parser.add_argument("--logs", type=Path, required=True)
    args = parser.parse_args()
    for name in ("lean_prefix", "verifier", "checker", "export_path", "sandbox", "logs"):
        setattr(args, name, getattr(args, name).resolve())
    args.logs.mkdir(parents=True, exist_ok=True)
    for relative, expected in PINNED_BLOBS.items():
        if git_blob(args.verifier / relative) != expected:
            raise RuntimeError("Pinned verifier file differs: " + relative)
    version = subprocess.check_output([args.lean_prefix / "bin/lean", "--version"], text=True)
    if LEAN_COMMIT not in version:
        raise RuntimeError("The compiler/exporter does not match the project's Lean pin")
    selected = json.loads((args.verifier / "checker-revisions.json").read_text())["con_ron"][SOURCE_TOOLCHAIN]
    if sha256(args.checker) != selected["binary_sha256"]:
        raise RuntimeError("Checker does not match the official selected binary digest")
    if sha256(args.export_path) != args.export_sha256:
        raise RuntimeError("Input export differs from the recorded protected export")

    # Load only the four exact upstream files authenticated above. Avoid
    # importing the full verifier and its workflow initialization.
    sys.path.insert(0, str(args.verifier / "scripts"))
    from kernel_outcomes import con_ron_outcome
    from verification_errors import VerificationError
    wanted = {"primitive_targets", "comparator_export_targets", "ill_typed_export"}
    tree = ast.parse((args.verifier / "scripts/verify_submission.py").read_text())
    nodes = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name in wanted]
    if len(nodes) != 3:
        raise RuntimeError("Missing official control functions")
    module = ast.Module(body=[ast.ImportFrom(module="__future__",
        names=[ast.alias(name="annotations")], level=0), *nodes], type_ignores=[])
    ast.fix_missing_locations(module)
    namespace = {"Path": Path, "re": re, "json": json, "VerificationError": VerificationError}
    exec(compile(module, "pinned-palomar-control-functions", "exec"), namespace)

    def sandbox(command, readable, writable=(), environment=None, cwd=Path("/tmp")):
        result = [str(args.sandbox), "--ro-bind", "/", "/", "--tmpfs", "/home",
            "--tmpfs", "/root", "--tmpfs", "/run/user", "--tmpfs", "/tmp",
            "--dir", "/tmp/home", "--dev", "/dev", "--proc", "/proc", "--clearenv",
            "--tmpfs", "/run", "--tmpfs", "/var"]
        for path in readable:
            result += ["--ro-bind", str(path), str(path)]
        for path in writable:
            result += ["--bind", str(path), str(path)]
        for key, value in (environment or {}).items():
            result += ["--setenv", key, value]
        return result + ["--setenv", "HOME", "/tmp/home", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
            "--unshare-all", "--die-with-parent", "--new-session", "--chdir", str(cwd),
            "--", *map(str, command)]

    def replay(label: str, export: Path):
        command = sandbox([args.checker, "--jobs=2", "--verified", export], [args.checker, export])
        started = time.monotonic()
        result = subprocess.run(command, env={}, capture_output=True, text=True, timeout=1800)
        (args.logs / (label + ".stdout.log")).write_text(result.stdout)
        (args.logs / (label + ".stderr.log")).write_text(result.stderr)
        outcome = con_ron_outcome(result.returncode, result.stdout, result.stderr)
        record = {"command": command, "elapsed_seconds": round(time.monotonic() - started, 3),
            "export_sha256": sha256(export), "outcome": outcome}
        print(json.dumps({"phase": label, "outcome": outcome}), flush=True)
        return record

    with tempfile.TemporaryDirectory(prefix="turan-con-ron-controls-") as temporary:
        work = Path(temporary)
        library = work / "lib"
        library.mkdir()
        source = work / "PalomarPreflightSolution.lean"
        source.write_text("theorem palomar_preflight : True := trivial\n")
        environment = {"LEAN_PATH": str(library) + ":" + str(args.lean_prefix / "lib/lean"),
            "PATH": str(args.lean_prefix / "bin") + ":/usr/bin:/bin"}
        compile_command = sandbox([args.lean_prefix / "bin/lean", "-o",
            library / "PalomarPreflightSolution.olean", source], [args.lean_prefix, work],
            [library], environment, work)
        compiled = subprocess.run(compile_command, env={}, capture_output=True, text=True, timeout=1800)
        (args.logs / "control-compile.log").write_text(compiled.stdout + compiled.stderr)
        if compiled.returncode != 0:
            raise RuntimeError("Control compilation failed: " + compiled.stderr)
        config = {"theorem_names": ["palomar_preflight"], "definition_names": [],
            "permitted_axioms": ["Classical.choice", "Quot.sound", "propext"]}
        targets = namespace["comparator_export_targets"](config,
            namespace["primitive_targets"](args.lean_prefix))
        positive, negative = work / "positive.export", work / "ill-typed.export"
        export_command = sandbox([args.lean_prefix / "bin/leanexport", "PalomarPreflightSolution",
            "--", *targets], [args.lean_prefix, work], environment=environment, cwd=work)
        with positive.open("wb") as output:
            exported = subprocess.run(export_command, env={}, stdout=output,
                stderr=subprocess.PIPE, timeout=1800)
        (args.logs / "control-export.log").write_bytes(exported.stderr)
        if exported.returncode != 0:
            raise RuntimeError("Control export failed: " + exported.stderr.decode(errors="replace"))
        negative.write_bytes(namespace["ill_typed_export"](positive, "palomar_preflight"))
        controls = [replay("control-positive", positive), replay("control-ill-typed", negative)]
        if [item["outcome"]["status"] for item in controls] != ["accepted", "rejected"]:
            raise RuntimeError("The checker failed its positive/ill-typed controls")
        control_record = {"status": "passed", "source": source.read_text(), "targets": targets,
            "controls": controls, "official_control_functions": PINNED_BLOBS}
        (args.logs / "controls.json").write_text(json.dumps(control_record, indent=2) + "\n")

    result = replay("solution", args.export_path)
    record = {"recorded_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_commit": VERIFIER_COMMIT, "selected_checker": selected,
        "checker_sha256": sha256(args.checker), "compiler_version": version.strip(),
        "sandbox_disabled": False, "positive_and_negative_controls_passed": True,
        "classifier_git_blob": PINNED_BLOBS["scripts/kernel_outcomes.py"],
        "public_palomar_workflow_run": False, "solution": result}
    (args.logs / "replay.json").write_text(json.dumps(record, indent=2) + "\n")
    # A recognized advisory decline is recorded as such, never as acceptance.
    return 0 if result["outcome"]["status"] in {"accepted", "declined"} else 1


if __name__ == "__main__":
    raise SystemExit(main())
