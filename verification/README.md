# Verification record

**Snapshot: 23 November 2026 (UTC). Formalization author and responsible maintainer: Xizhi Liu.**

The complete Lean proof, all-source Lake replay and transitive axiom audit passed. **Independent statement comparison and the mandatory Lean/NanoDa replays passed, with Comparator exit code 0.** The officially selected con-ron returned a recognized `fuel-exhausted` advisory decline after its positive and ill-typed controls passed. This is not con-ron acceptance. Public Palomar full preflight and independent human mathematical review have not been performed.

This directory records local evidence, with [report.json](report.json) as its machine-readable companion. It is not an official Palomar acceptance certificate.

## Result and mathematical scope

The solution exports the following theorem, without additional mathematical hypotheses:

```lean
theorem TranscendentalTuran.main_result :
    ∃ n : ℕ, ∃ P : TuranUniversality.RGraph (Fin n) 3,
      P.edges.Nonempty ∧
      Transcendental ℚ (TuranUniversality.turanDensity P)
```

The witness is `Construction.singleGraph`. Ordinary containment uses a globally injective vertex map preserving edges, including isolated forbidden vertices. The proved density is the ordinary extremal edge count divided by `n.choose 3`; `singleGraph_extremalDensity_tendsto` establishes convergence to the stated value. The exact source-class optimization identity, both of its inequalities, and the transfer to this actual single forbidden graph are proved and assembled. These are theorems of the completed solution, rather than remaining hypotheses of the main result.

The independently stated `Challenge.lean` imports only Mathlib and restates the relevant definitions. It contains the single deliberate target `sorry` used for comparison. It is absent from the Solution import closure. Its successful separate build checks that the Challenge file is accepted as a target; it does not prove the target theorem. The solution proves the theorem independently. Comparator has checked the correspondence between those environments, including the relevant definitions and permitted axioms.

## Recorded checks

| Check | Result and scope | Evidence |
| --- | --- | --- |
| All local Lean modules | **322 / 322 passed**, with no failed or blocked module in the final record | [all-source-build.json](all-source-build.json), [all-source-build.log](all-source-build.log) |
| Current source integrity | All **322** current source hashes match the successful build record; no missing or extra source module | [lean-sources.sha256](lean-sources.sha256), [report.json](report.json) |
| Default Lake target | `lake build` completed successfully, reporting **3,941 jobs** | [default-build.log](default-build.log) |
| Solution entry point | The complete `Solution` target built successfully | [Solution.log](Solution.log) |
| Source requirements | `scripts/check-lean-sources.py` returned **0**; all 322 files have valid module headers and meet the line limit | [report.json](report.json) |
| Solution hole and dependency check | Solution reaches **316 local modules** and does not import Challenge; the only `sorry` token in comment-stripped local source is the intentional Challenge target | [report.json](report.json) |
| Transitive axiom audit | **13 declarations**, each depending on exactly `propext`, `Classical.choice`, and `Quot.sound` | [axioms.txt](axioms.txt), [axiom-audit.log](axiom-audit.log) |
| Executable constructor | Regular computable constructor compiled; `(buildSingleGraph false).isNone` evaluated to **true** | [ExecutableWitness log](TranscendentalTuran.Construction.ExecutableWitness.log) |
| Mandatory Comparator | **Passed, exit 0:** independent statement/definition comparison, permitted axioms, NanoDa and Lean default kernel | [mandatory-comparator.log](mandatory-comparator.log), [mandatory-comparator.json](mandatory-comparator.json) |
| Mandatory checker controls | **Passed:** valid proof accepted; mismatched statement, forbidden axiom and well-formed ill-typed proof rejected | [summary](mandatory-controls/summary.json), [full run](mandatory-controls/attempt-2/result.json) |
| Selected con-ron | **Recognized advisory decline: `fuel-exhausted`**; positive accepted / ill-typed rejected controls passed | [replay](con-ron-selected/replay.json), [controls](con-ron-selected/controls.json) |
| Pinned official metadata contract | **Passed** using byte-authenticated validator files | [metadata-validator.json](metadata-validator.json) |
| Public Palomar full preflight | **Not run** | Pinned workflow in `.github/workflows/palomar-preflight.yml` |
| Independent human review | **Not performed** | Review status in `formalization.yaml` |

The all-source scheduler invokes genuine `lake --fail-fast build +<module>` commands in dependency order, with two concurrent Lake invocations configured. The final record contains one successful attempt for each module, and its recorded SHA-256 values were independently recomputed against the current files while preparing this report.

These records include ordinary Lake cache reuse and replay. They do not claim a fresh zero-cache rebuild of every dependency. Similarly, the 3,941 default-build jobs are Lake jobs, including dependencies and replayed artifacts; they are not a count of local source files freshly elaborated during that pass.

The local source inventory comprises 246 modules under the `TranscendentalTuran` prefix, 74 under `TuranUniversality`, and the separate `Solution` and `Challenge` entry points. It has 44,158 physical lines; the largest module has 494 lines. The source-hash manifest covers these 322 files, including the intentional Challenge target, and excludes downloaded `.lake` dependency sources. Dependency revisions are recorded separately in `lake-manifest.json`.

## Axiom audit and executable construction

`TranscendentalTuran/Audit.lean` requests Lean's **transitive** axiom dependencies for the final theorem and twelve principal interfaces, including the executable constructor, density value and limit, source-class identity, source upper and lower bounds, source gain, single-graph transfer, and arithmetic transcendence. All thirteen requested names are present in [axioms.txt](axioms.txt), and every reported set is exactly the permitted standard three. No additional axiom or `sorryAx` occurs in these audited dependency sets.

A supplementary scan of comment-stripped local source found no `admit`, custom `axiom` declaration, `native_decide`, or explicit `sorryAx` token. The sole `sorry` is in Challenge. This textual scan complements the semantic axiom audit; it is not a replacement for it.

`Construction.buildSingleGraph : Bool → Option (FiniteGraph 3)` is a regular compiled definition, not merely a macro whose executable code has been deferred. Its enabled branch is definitionally `some singleGraph`, and `executable_main_result` proves that output has a nonempty edge set and transcendental ordinary density. Compilation checks the executable dependency chain. The axiom audit includes logical proof fields, so the standard classical axioms in that audit do not imply that the runtime graph data are computed using a noncomputable choice.

**The enabled construction has not been executed, and the complete graph has not been materialized.** The graph is astronomically large. Only the disabled branch was evaluated, as recorded in the constructor log. The correctness theorem for the enabled branch is a symbolic Lean proof.

## Independent comparison and checker outcomes

The final mandatory Comparator run used the pinned original Lean compiler,
exporter and kernels. It checked the separately stated Challenge against
Solution and ended with:

```text
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

The process exited **0**. Its configuration, executable hashes, exact export
hashes, timing and invocation are in [mandatory-comparator.json](mandatory-comparator.json).
This final invocation replayed the same exports generated by the bundled
`leanexport` during the earlier sandboxed source-build run. It did not generate
new proofs or edit exports. All 322 source hashes were checked again before
replay. [export-fingerprints.json](export-fingerprints.json) identifies the
42,020,457-byte Challenge export and the 478,216,624-byte solution export. These
large generated files are not included in the source archive.

### Authenticated advisory con-ron replay

The pinned official [checker manifest](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/checker-revisions.json)
selects con-ron from release `v4.36.0-rc1` for source toolchain `v4.35.0-rc2`.
The downloaded release archive and the extracted executable both matched their
manifest SHA-256 values; the receipt is in
[con-ron-selected/download-receipt.json](con-ron-selected/download-receipt.json).
The freshly authenticated executable is byte-identical to the already installed
bundled con-ron. The compiler, exporter, Lean kernel and NanoDa were not changed.

The selected checker ran with exactly `--jobs=2 --verified`, in the retained
sandbox, on the same protected solution export. Its official controls were
constructed using the exact pinned `primitive_targets`,
`comparator_export_targets` and `ill_typed_export` functions:

| Input | Actual result |
| --- | --- |
| `theorem palomar_preflight : True := trivial` | Accepted 466 declarations, exit 0. |
| The same well-formed export with the theorem proof replaced by its type | Rejected as a type mismatch, exit 1. |
| Complete main-theorem export | Exit 3 with a unique fuel-exhaustion diagnostic at `TranscendentalTuran.Optimization.Paper.A_eval_eq`. |

The byte-authenticated official `con_ron_outcome` function classified the last
result as **`declined / fuel-exhausted`**. The
[pinned classifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/kernel_outcomes.py)
and [verification policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/SECURITY.md)
treat this recognized limitation as advisory after mandatory acceptance and
successful controls. Unknown errors and actual rejections still block. The
full result and logs are under `con-ron-selected/`.

**The complete proof has not been accepted by con-ron.** The successful
independent kernel acceptances are Lean and NanoDa. No proof was changed to
produce the decline, and no checker limit or trusted mode was relaxed.

### Preserved earlier attempts and local isolation

The first invocation stopped before building Challenge because the host denied
the `NETLINK_ROUTE` socket bubblewrap uses to initialize loopback. Its
[log](comparator.log) and [exit record](comparator-exit.json) are retained. The
[local adapter and observed probes](isolation/README.md) preserve the sandbox
while first creating a fresh private network namespace; every adapted phase is
offline. Original read-only mounts, environment clearing, process/session
isolation and lifecycle restrictions remain, and capabilities are explicitly
dropped. No no-sandbox option was used.

The initial strict combined invocation then passed comparison and both
mandatory kernels, but its default-worker con-ron exited **137 without a
verdict**, making that whole invocation exit 1. That failure remains recorded
in [comparator-isolated.log](comparator-isolated.log) and
[comparator-isolated-exit.json](comparator-isolated-exit.json). Its exact script
is preserved in `history/verify-comparator-initial.sh`. The later two-worker
recognized decline does not retrospectively classify the earlier 137 as an
OOM or an allowed decline.

The current `scripts/verify-comparator.sh` follows the pinned policy's mandatory
phase, while `scripts/replay-con-ron.py` performs the separately classified
local advisory replay with controls. That separation follows the actual
pinned official verifier; it does not claim every checker accepted the proof.

### Public verification still separate

The official workflow is configured for `mode: full` and
`execution_profile: palomar-standard-v1`, at the pinned verifier revision below.
It has not been run on a specified public repository commit. Public runner
supervision, the complete official pipeline, registry review and acceptance
remain separate. No independent human mathematical review is claimed.
Local kernel acceptance establishes the formal theorem; the documented
source-to-formalization correspondence remains available for human review.

## Versions

| Component | Pin or observed version |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc2` |
| Observed Lean executable | `4.35.0-rc2`, `x86_64-unknown-linux-gnu`, Release |
| Lean commit | `11acb17ec6b07a8f9e9173e6845197929540936b` |
| Mathlib revision | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Palomar verifier revision | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` |
| Palomar template revision | `2891de4c48955af824969a263d31b25e7a9a1406` |

The observed installed Mathlib Git HEAD matches the configured pin. All nine resolved dependency revisions from `lake-manifest.json` are included in `report.json`. The Palomar entries identify the configured tools and workflow; they do not assert that the public preflight ran.

## Reproduce without overwriting retained evidence

Run these commands from the repository root with the pinned Lean toolchain, Python 3, and the required dependencies available:

```sh
lake exe cache get
python3 scripts/check-lean-sources.py
sha256sum --check verification/lean-sources.sha256
python3 scripts/build-bounded.py --all --jobs 2 --log-dir /tmp/transcendental-turan-recheck
lake build
lake build +Solution
python3 scripts/audit-axioms.py --log /tmp/transcendental-turan-recheck-axioms.txt
```

Use `--jobs 1` for a lower-memory all-source replay. The source manifest paths are relative to the repository root, so its integrity command must be run there. The audit command imports the completed development, without importing Challenge. Write new logs to new paths so the original evidence remains available.

The separate independent check is:

```sh
bash scripts/verify-comparator.sh
```

It requires a compatible `bwrap` environment and the toolchain's bundled checker executables. The script performs the independent Challenge/Solution comparison and mandatory Lean/NanoDa replays. The separately classified local con-ron replay is implemented in `scripts/replay-con-ron.py`; it requires the authenticated pinned verifier files, selected checker and protected export identified by SHA-256. Run that script with `--help` for its explicit path arguments. The pinned public workflow runs the complete official pipeline on a reviewed public commit.
