# A Three-Graph with Transcendental Turán Density

Formalization author and responsible maintainer: **Xizhi Liu**.

Public repository: [xliu2022/transcendental-turan-lean](https://github.com/xliu2022/transcendental-turan-lean).
See [README_zh.md](README_zh.md) for the Chinese guide.

This project completes the Lean proof of the main theorem of the manuscript
dated 18 November 2026: an explicitly computable finite ordinary 3-uniform
hypergraph has transcendental ordinary Turán density. The main theorem has no
additional mathematical hypotheses.

## Proved result

The complete result is exported by `Solution.lean` through
`TranscendentalTuran.Main`:

```lean
theorem TranscendentalTuran.main_result :
    ∃ n : ℕ, ∃ P : TuranUniversality.RGraph (Fin n) 3,
      P.edges.Nonempty ∧
      Transcendental ℚ (TuranUniversality.turanDensity P)
```

The witness is `Construction.singleGraph`. Its density is

\[
  \pi(P)=6\,\Psi\!\left(22-\frac{1024}{15\pi}\right).
\]

Here `Ψ` is the manuscript's exact compact-domain rational optimization
problem with free individual root weights. The proof identifies the actual
source-class supremum with that maximum. `singleGraph_extremalDensity_tendsto`
also proves that the ordinary binomial-normalized extremal densities converge
to the displayed value.

Ordinary containment requires a globally injective vertex map, including on
isolated forbidden vertices. The independent `Challenge.lean` restates the
finite-graph, embedding, extremal-number and density definitions using only
Mathlib. It contains one deliberate target hole. No proof module imports it.

## Executable construction

`Construction.buildSingleGraph : Bool → Option (FiniteGraph 3)` is a regular
compiled function. Its enabled branch is definitionally `some singleGraph`,
and `executable_main_result` proves the output has a nonempty edge set and
transcendental ordinary density.

The algorithm enumerates the actual finite guarded obstruction basis, indexes
it using explicit encodings, takes private pair extensions and their categorical
product, and labels the result by a finite interval. The exact disjoint-clique
guard uses an arithmetic product labeling. All graph data in this path are
computable; classical choices used to prove guard embeddings do not compute
the witness.

The graph is astronomically large. Compilation checks the executable dependency
chain, and a disabled-branch evaluation checks module initialization. The enabled
construction has not been evaluated. Inlining annotations prevent eager
initialization, and symbolic finite-set/family lemmas prevent proof elaboration
from evaluating the concrete enumeration. These are implementation choices,
not additional mathematical assumptions.

## Verification status

**The complete Lean proof, all-source build and final transitive axiom audit
have passed.** This includes the exact density identity, ordinary density limit,
executable constructor and both source-class inequalities, with all auxiliary
mathematical hypotheses discharged.

| Check | Recorded result |
| --- | --- |
| All-source Lake replay | **322 / 322** local Lean modules passed, including the separately checked independent Challenge. |
| Default `lake build` | **3,941 jobs**, completed successfully; see [the build log](verification/default-build.log). |
| Final transitive axiom audit | **13 declarations** audited, including the main theorem and executable constructor; every dependency list is exactly `propext`, `Classical.choice`, and `Quot.sound`. See [the axiom report](verification/axioms.txt). |
| Source-integrity checks | All 322 files have valid module headers; no solution `sorry`, custom axioms or `native_decide` uses were found. |
| Independent statement and definition comparison | **Passed** in an isolated Comparator invocation, together with the permitted-axiom check. |
| Mandatory Comparator and kernel replays | **Exit 0:** independent comparison, permitted axioms, Lean default kernel and NanoDa all passed. The final replay used the same byte-checked exports; see [its record](verification/mandatory-comparator.json) and [log](verification/mandatory-comparator.log). |
| Mandatory checker controls | **Passed:** valid proof accepted; statement mismatch, forbidden axiom and well-formed ill-typed proof rejected. Both Lean and NanoDa rejected the ill-typed proof. See [the controls](verification/mandatory-controls/summary.json). |
| Selected con-ron replay | **Recognized advisory decline: `fuel-exhausted`**, exit 3, at `TranscendentalTuran.Optimization.Paper.A_eval_eq`. This is not con-ron acceptance. See [the exact replay record](verification/con-ron-selected/replay.json). |
| con-ron controls | **Passed:** the positive control accepted 466 declarations; the ill-typed negative control was rejected. See [the control record](verification/con-ron-selected/controls.json). |
| Original strict combined invocation | **Overall exit 1:** its con-ron phase exited 137 without a diagnostic. The original [log](verification/comparator-isolated.log) and [exit record](verification/comparator-isolated-exit.json) are retained as a failed invocation. |
| Public Palomar full preflight and registry review | **Not run.** A public repository and its full 40-character commit SHA are needed for the pinned public workflow. |

The audit targets are listed in `TranscendentalTuran/Audit.lean` and the permitted
axioms in `comparator.json`. The independent Challenge contains one deliberate
target hole; no solution module imports it, and it is excluded from the
solution's zero-hole claim. The first sandbox-setup failure caused by the
workspace's `NETLINK_ROUTE` restriction remains in
[its log](verification/comparator.log) and
[invocation record](verification/comparator-exit.json). The later isolated
invocation used the documented compatibility mechanism in
`verification/isolation/README.md` and completed the independent comparison
and both mandatory kernel replays.

The pinned Palomar manifest selects con-ron from Lean release `v4.36.0-rc1`
for this source toolchain. The official release archive and extracted executable
both matched their pinned SHA-256 values; see
[the download receipt](verification/con-ron-selected/download-receipt.json).
The authenticated executable has the same digest as the local bundled one.
Its separate replay used exactly `--jobs=2 --verified` on the same protected
solution export. The byte-authenticated official classifier recorded the
fuel-exhaustion decline, which the pinned policy treats as advisory after
mandatory acceptance and successful controls. This neither converts the
original exit 137 into a recognized decline nor claims con-ron acceptance.

## Reproduce the checks

Pinned versions:

- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- Palomar verifier: `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.

With the pinned Lean toolchain and Python available:

```sh
bash verify.sh --checks-only
bash verify.sh
```

The first command checks source requirements and project metadata without
installing dependencies. The second fetches the pinned Mathlib cache, builds
every local module with bounded concurrency, and audits the final axioms.
It writes fresh logs to a temporary directory and preserves the checked-in
verification evidence. Ruby is required for metadata validation; set
`TURAN_BUILD_JOBS=1` to reduce compiler concurrency. On a compatible Linux
host with bubblewrap, `bash verify.sh --comparator` additionally runs the
mandatory independent comparison and Lean/NanoDa checks.

The individual commands are:

```sh
lake exe cache get
python3 scripts/check-lean-sources.py
python3 scripts/build-bounded.py --all --jobs 2
lake build
lake build Solution
python3 scripts/audit-axioms.py
./scripts/verify-comparator.sh
```

The bounded scheduler uses genuine Lake builds in dependency order and limits
concurrent compiler processes; `--jobs 1` uses less memory. It does not supply
compiler artifacts or bypass dependency checks. The Comparator script uses
`bwrap` for the independent comparison, permitted-axiom check, Lean kernel and
NanoDa mandatory phase. `scripts/replay-con-ron.py` separately checks the pinned
verifier sources, authenticates the selected executable, runs its positive and
ill-typed controls, and classifies its replay of a hash-checked protected export.
Its required input paths and export digest are listed by `--help`. The official
release archive must also be authenticated against the pinned manifest before
extracting the checker. The comparison and checker phases use the documented Lake-style sandbox.
The convenience script runs `lake exe cache get` before Comparator as a local
preparation step; it does not reproduce the official outer supervisor and
its stronger isolation policy. The workspace compatibility mechanism is
documented in `verification/isolation/README.md`. The pinned public workflow
runs the complete official pipeline.

## Mathematical organization

| Directory | Content |
| --- | --- |
| `Construction/` | Parameters, exact guard, actual root completion/localization, type surgery, source value and effective single graph |
| `Encoding/` | Positive declarations, all seventeen rooted rules, bounded violation certificates and the decidable finite basis |
| `Network/` | Actual layer energy, partial-bijection series reduction, owner coordinates, private leaves and source gain |
| `Green/` | Actual quadrant walks, exact Green evaluation, finite networks and finite lower realizations |
| `Optimization/` | Exact free-root objective, compact domain, strict type budgets and arithmetic reduction |
| `Algebra/` | Rational real quantifier elimination and the algebraic-minimum argument |
| `Transfer/` | Ordinary embeddings, two-dimensional tables, factor recovery and ordinary-density transfer |
| `Core/` | Finite weighted maxima and the normalization by `3! = 6` |
| `External/Pi/` | Ported proof of π transcendence with source attribution |
| `TuranUniversality/` | Reused hypergraph and density dependency closure |

All but the final row are relative to `TranscendentalTuran/`.
See `docs/PROOF_MAP.md` for the mathematical interfaces, discharged hypotheses,
limit order and documented proof adaptations.

## Source fidelity and attribution

The manuscript's bibliographic author field is blank; the formalization
authorship follows the user's explicit instruction and does not infer
manuscript authorship. The main conclusion and density normalization agree with
the manuscript. Documented proof adaptations include the guard's cubic bound,
private extensions for all core pairs, full finite-box Green vectors, exact
reservoir-error limits, partial-bijection series inequalities, recurrence-based
walk counting and use of Mathlib's proved Wallis limit.

Source fingerprints, import-only patches and original licenses are retained in
`provenance/`, `Algebra/Legacy/` and `External/Pi/`. Targeted imports replace broad
imports in five reused TuranUniversality modules; their declaration and proof
bodies are unchanged. The π port's import changes are separately recorded.
The project is licensed under Apache-2.0; reused sources retain their original
notices. Development used AI assistance and has not received independent human
mathematical review.

## Palomar submission

Use the public repository `xliu2022/transcendental-turan-lean` and the full
40-character SHA of the pushed commit to be reviewed. The Lean project is
at the repository root; the configuration is `comparator.json` and the metadata
is `formalization.yaml`. The optional project and metadata path fields on the
submission form can be left blank for this layout. Copy the immutable SHA with
`git rev-parse HEAD` after committing and pushing the intended snapshot.

The manually triggered `.github/workflows/palomar-preflight.yml` invokes the
official verifier at the pinned commit, with `mode: full` and
`execution_profile: palomar-standard-v1`. It has not been run. Its public
submission requires a public source repository and the full 40-character SHA
of the reviewed commit. The official submission form is
https://submit.palomar-registry.org/ .

Follow [Palomar's submission guide](https://palomar-registry.org/how-to-submit)
for the current requirements. Running the preflight does not submit or register
the result; registration is a separate step after verification and review.

The metadata has passed the pinned official `load_formalization_metadata`
validator. This checks the metadata contract. Public full verification,
registry review and independent human mathematical review remain separate
from the completed local Lean proof, axiom audit, independent comparison and
mandatory kernel acceptance. The local con-ron result is a recognized advisory
decline. No official Palomar acceptance is claimed.
