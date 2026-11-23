#!/usr/bin/env python3
"""Run the pinned Palomar mandatory Lean/NanoDa small controls locally.

Only fresh Init-only fixtures are compiled. No project Lean module is imported,
and no main-proof replay or public Palomar workflow is performed. The existing
isolation-preserving local bubblewrap adapter is retained throughout.
"""

from __future__ import annotations

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


VERIFIER_COMMIT = "14aa8d6b3c2f14a8540605e37144560b9a00e7e7"
LEAN_COMMIT = "11acb17ec6b07a8f9e9173e6845197929540936b"
PINNED_BLOBS = {
    "scripts/verify_submission.py": "35afd78fbc4ba9ecd43a617f99ab8f9a4f376842",
    "scripts/verification_errors.py": "b4665f25e2492d5ce86a3955e208211043e84c92",
}
WRAPPER_SHA256 = "be116b0142850cf2d8a6cd4f3f6c881ab0762b39aee2656d13b9f991bf3b54e4"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-prefix", type=Path, required=True)
    parser.add_argument("--verifier", type=Path, required=True)
    parser.add_argument("--sandbox", type=Path, required=True)
    parser.add_argument("--logs", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    for key in ("lean_prefix", "verifier", "sandbox", "logs"):
        setattr(args, key, getattr(args, key).resolve())
    args.logs.mkdir(parents=True, exist_ok=True)
    if (args.logs / "result.json").exists() or list(args.logs.glob("*.stdout.log")):
        raise RuntimeError("The output directory already contains a run; use a fresh --logs directory")
    for relative, digest in PINNED_BLOBS.items():
        if git_blob(args.verifier / relative) != digest:
            raise RuntimeError("Pinned verifier bytes differ: " + relative)
    if sha256(args.sandbox) != WRAPPER_SHA256:
        raise RuntimeError("The frozen isolation adapter differs")
    version = subprocess.check_output([args.lean_prefix / "bin/lean", "--version"], text=True)
    if LEAN_COMMIT not in version:
        raise RuntimeError("The compiler does not match the pinned Lean commit")

    # Reuse the exact authenticated upstream target selection, tampering, export
    # format check, and verdict classifier. Do not initialize the full workflow.
    sys.path.insert(0, str(args.verifier / "scripts"))
    sys.dont_write_bytecode = True
    from verification_errors import VerificationError
    functions = {
        "primitive_targets", "comparator_export_targets", "ill_typed_export",
        "verify_export", "comparator_failure_excerpt", "comparator_verdict",
    }
    constants = {
        "STANDARD_AXIOMS", "COMPARATOR_VERDICT_RE", "COMPARATOR_KERNEL_REJECTED_RE",
        "COMPARATOR_LEAN_KERNEL", "COMPARATOR_INFRASTRUCTURE_RE",
        "COMPARATOR_FAILURE_MARKERS", "RETRY_SAME_COMMIT",
    }
    tree = ast.parse((args.verifier / "scripts/verify_submission.py").read_text())
    selected = []
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in functions:
            selected.append(node)
        elif isinstance(node, ast.Assign) and any(
            isinstance(target, ast.Name) and target.id in constants for target in node.targets
        ):
            selected.append(node)
    if {node.name for node in selected if isinstance(node, ast.FunctionDef)} != functions:
        raise RuntimeError("An expected pinned control helper is absent")
    module = ast.Module(body=[ast.ImportFrom(module="__future__",
        names=[ast.alias(name="annotations")], level=0), *selected], type_ignores=[])
    ast.fix_missing_locations(module)
    upstream = {"Path": Path, "json": json, "re": re, "VerificationError": VerificationError}
    exec(compile(module, "authenticated-palomar-control-helpers", "exec"), upstream)

    tool_names = ["lean", "leanexport", "lake", "leanchecker", "nanoda_bin"]
    record = {
        "schema_version": 1,
        "scope": "Local mandatory Lean/NanoDa small controls from pinned Palomar comparator_preflight",
        "status": "running",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "verifier_commit": VERIFIER_COMMIT,
        "authenticated_source_blobs": PINNED_BLOBS,
        "authenticated_helper_functions": sorted(functions),
        "compiler_version": version.strip(),
        "tools": {name: {"path": str(args.lean_prefix / "bin" / name),
                         "sha256": sha256(args.lean_prefix / "bin" / name)} for name in tool_names},
        "sandbox": {"adapter": str(args.sandbox), "adapter_sha256": sha256(args.sandbox),
                    "disabled": False, "read_only_root": True, "masked_home_and_tmp": True,
                    "unshare_all": True, "new_session": True, "die_with_parent": True,
                    "clear_environment": True, "fresh_private_network": True,
                    "all_capabilities_dropped": True},
        "project_lean_imported": False,
        "main_proof_replayed": False,
        "public_palomar_full_workflow_run": False,
        "con_ron_scope": "Checked separately by the coordinating process; not repeated here.",
        "steps": [],
        "controls": [],
    }

    def persist():
        (args.logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")

    def sandbox(command, readable, writable=(), environment=None, cwd=Path("/tmp")):
        argv = [str(args.sandbox), "--ro-bind", "/", "/",
            "--tmpfs", "/home", "--tmpfs", "/root", "--tmpfs", "/run/user",
            "--tmpfs", "/tmp", "--dir", "/tmp/home", "--dev", "/dev",
            "--proc", "/proc", "--clearenv", "--tmpfs", "/run", "--tmpfs", "/var"]
        for path in readable:
            argv.extend(["--ro-bind", str(path), str(path)])
        for path in writable:
            argv.extend(["--bind", str(path), str(path)])
        for key, value in (environment or {}).items():
            argv.extend(["--setenv", key, value])
        return argv + ["--setenv", "HOME", "/tmp/home", "--setenv", "LEAN_ABORT_ON_PANIC", "1",
            "--unshare-all", "--die-with-parent", "--new-session", "--chdir", str(cwd),
            "--", *map(str, command)]

    def run(label, command, *, export_to=None):
        if sha256(args.sandbox) != WRAPPER_SHA256:
            raise RuntimeError("Isolation adapter changed during the run")
        started = time.monotonic()
        print(json.dumps({"phase": label, "status": "running"}), flush=True)
        stdout_path = args.logs / (label + ".stdout.log")
        stderr_path = args.logs / (label + ".stderr.log")
        try:
            if export_to is not None:
                with export_to.open("xb") as output:
                    proc = subprocess.run(command, env={}, stdout=output, stderr=subprocess.PIPE,
                                          timeout=180, check=False)
                stdout = ""
                stdout_path.write_text("Export bytes retained separately: " + export_to.name + "\n")
                stderr_path.write_bytes(proc.stderr)
                stderr = proc.stderr.decode(errors="replace")
            else:
                proc = subprocess.run(command, env={}, capture_output=True, text=True,
                                      timeout=180, check=False)
                stdout, stderr = proc.stdout, proc.stderr
                stdout_path.write_text(stdout)
                stderr_path.write_text(stderr)
        except subprocess.TimeoutExpired as error:
            stdout_path.write_bytes(error.stdout or b"")
            stderr_path.write_bytes(error.stderr or b"")
            record["steps"].append({"label": label, "command": command, "status": "timeout",
                "elapsed_seconds": round(time.monotonic() - started, 3)})
            persist()
            raise
        result = {"label": label, "command": command, "exit_code": proc.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "stdout_log": stdout_path.name, "stderr_log": stderr_path.name}
        record["steps"].append(result)
        persist()
        print(json.dumps({"phase": label, "exit_code": proc.returncode}), flush=True)
        return proc.returncode, stdout, stderr

    persist()
    try:
        with tempfile.TemporaryDirectory(prefix="turan-mandatory-controls-") as temporary:
            work = Path(temporary)
            source, library, exports = work / "src", work / "lib", work / "exports"
            for directory in (source, library, exports):
                directory.mkdir()
            fixtures = {
                "PalomarPreflightChallenge": "theorem palomar_preflight : True := trivial\n",
                "PalomarPreflightSolution": "theorem palomar_preflight : True := trivial\n",
                "PalomarPreflightWrong": "theorem palomar_preflight : True ∧ True := ⟨trivial, trivial⟩\n",
                "PalomarPreflightIllegalAxiom": (
                    "axiom palomar_forbidden : True\n"
                    "theorem palomar_preflight : True := palomar_forbidden\n"),
            }
            config = {"challenge_module": "PalomarPreflightChallenge",
                "solution_module": "PalomarPreflightSolution", "theorem_names": ["palomar_preflight"],
                "definition_names": [], "permitted_axioms": sorted(upstream["STANDARD_AXIOMS"]),
                "external_kernels": {"nanoda": [str(args.lean_prefix / "bin/nanoda_bin")]}}
            config_path = work / "comparator.json"
            config_path.write_text(json.dumps(config, indent=2) + "\n")
            primitives = upstream["primitive_targets"](args.lean_prefix)
            targets = upstream["comparator_export_targets"](config, primitives)
            record.update({"fixtures": fixtures, "comparator_configuration": config,
                           "primitive_targets": primitives, "export_targets": targets})
            env = {"PATH": str(args.lean_prefix / "bin") + ":/usr/bin:/bin",
                   "LEAN_PATH": str(library) + ":" + str(args.lean_prefix / "lib/lean"),
                   "TMPDIR": "/tmp"}
            for name, text in fixtures.items():
                src = source / (name + ".lean")
                src.write_text(text)
                command = sandbox([args.lean_prefix / "bin/lean", "-o", library / (name + ".olean"), src],
                    [args.lean_prefix, work], [library], env, work)
                code, _, stderr = run("compile-" + name, command)
                if code:
                    raise RuntimeError("Control compilation failed: " + stderr)
                output = exports / (name + ".export")
                command = sandbox([args.lean_prefix / "bin/leanexport", name, "--", *targets],
                    [args.lean_prefix, work], environment=env, cwd=work)
                code, _, stderr = run("export-" + name, command, export_to=output)
                if code:
                    raise RuntimeError("Control export failed: " + stderr)
                upstream["verify_export"](output)

            positive = exports / "PalomarPreflightSolution.export"
            ill_typed = exports / "PalomarPreflightIllTyped.export"
            ill_typed.write_bytes(upstream["ill_typed_export"](positive, "palomar_preflight"))
            upstream["verify_export"](ill_typed)
            before = [json.loads(line) for line in positive.read_bytes().splitlines() if line.strip()]
            after = [json.loads(line) for line in ill_typed.read_bytes().splitlines() if line.strip()]
            changed = [i for i, (a, b) in enumerate(zip(before, after)) if a != b]
            if len(before) != len(after) or len(changed) != 1:
                raise RuntimeError("The ill-typed export changed more than one declaration record")
            delta = changed[0]
            if after[delta]["thm"]["value"] != before[delta]["thm"]["type"]:
                raise RuntimeError("The ill-typed mutation is not proof := type")
            record["ill_typed_mutation"] = {"well_formed_ndjson": True,
                "record_count_unchanged": True, "changed_record_count": 1,
                "only_change": "palomar_preflight theorem value replaced by its type",
                "changed_record_index": delta}
            retained = args.logs / "exports"
            retained.mkdir()
            for exported in sorted(exports.glob("*.export")):
                shutil.copyfile(exported, retained / exported.name)
            record["exports"] = [{"path": "exports/" + p.name, "sha256": sha256(p),
                                  "bytes": p.stat().st_size} for p in sorted(retained.glob("*.export"))]
            persist()

            cases = [
                ("PalomarPreflightSolution", 0, None),
                ("PalomarPreflightWrong", 1, "comparator.rejected"),
                ("PalomarPreflightIllTyped", 1, "comparator.rejected"),
                ("PalomarPreflightIllegalAxiom", 1, "comparator.illegal_axiom"),
            ]
            for name, expected_exit, expected_code in cases:
                scratch = work / ("judge-" + name)
                project, temporary = scratch / "project", scratch / "tmp"
                project.mkdir(parents=True)
                temporary.mkdir()
                judge_env = {"PATH": str(args.lean_prefix / "bin") + ":/usr/bin:/bin",
                    "TMPDIR": str(temporary), "COMPARATOR_BWRAP": str(args.sandbox)}
                command = sandbox([args.lean_prefix / "bin/lake", "comparator", "--config", config_path,
                    "--challenge-from-export", exports / "PalomarPreflightChallenge.export",
                    "--solution-from-export", exports / (name + ".export")],
                    [args.lean_prefix, work, args.sandbox], [scratch], judge_env, project)
                code, stdout, stderr = run("judge-" + name, command)
                log = (stdout + "\n" + stderr).strip()
                verdict = upstream["comparator_verdict"](code, log)
                verdict_code = None if verdict is None else verdict.code
                checks = {"expected_exit_code": code == expected_exit,
                          "expected_pinned_verdict": verdict_code == expected_code}
                if name == "PalomarPreflightSolution":
                    checks.update({"success_marker": "Your solution is okay!" in log,
                        "lean_accepted": "Lean default kernel accepts the solution" in log,
                        "nanoda_accepted": "nanoda kernel accepts the solution" in log})
                elif name == "PalomarPreflightWrong":
                    checks["statement_mismatch_marker"] = (
                        "Challenge and solution theorem statement do not match" in log)
                elif name == "PalomarPreflightIllTyped":
                    rejected = upstream["COMPARATOR_KERNEL_REJECTED_RE"].findall(log)
                    checks.update({"lean_rejected": "Lean default" in rejected,
                                   "nanoda_rejected": "nanoda" in rejected})
                elif name == "PalomarPreflightIllegalAxiom":
                    checks["illegal_axiom_marker"] = bool(re.search(
                        r"^error: Illegal axiom detected: ", log, re.M))
                passed = all(checks.values())
                record["controls"].append({"fixture": name, "status": "passed" if passed else "failed",
                    "exit_code": code, "pinned_verdict_code": verdict_code,
                    "checks": checks, "stdout_log": "judge-" + name + ".stdout.log",
                    "stderr_log": "judge-" + name + ".stderr.log"})
                persist()
                if not passed:
                    raise RuntimeError("Control did not obtain the required verdict: " + name)
            record["status"] = "passed"
            record["mandatory_controls_passed"] = True
    except Exception as error:
        record["status"] = "failed_or_incomplete"
        record["mandatory_controls_passed"] = False
        record["failure"] = {"type": type(error).__name__, "message": str(error)}
        raise
    finally:
        record["finished_utc"] = datetime.now(timezone.utc).isoformat()
        persist()
    print(json.dumps({"status": record["status"], "mandatory_controls_passed": True}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
