# Mathematical interfaces and source alignment

Formalization author and responsible maintainer: **Xizhi Liu**.

## Status of this document

The complete Lean proof is finished. The source-class upper bound, the complete
finite lower realization, both sequential limits, the exact source value,
the effective single-graph transfer and the final main theorem are proved
without additional mathematical hypotheses. All 322 local Lean modules passed
the final genuine Lake replay, and the default build completed 3,941 jobs.
The final transitive audit of 13 declarations found exactly `propext`,
`Classical.choice`, and `Quot.sound` in every dependency list.

The regular executable constructor has compiled; only its disabled branch was
evaluated. An isolated Comparator invocation passed the independent statement
and definition comparison and the permitted-axiom check; Lean's default kernel
and NanoDa both accepted the solution. Its original combined con-ron phase
exited 137, leaving that strict invocation at overall exit 1. A separate replay
following the fixed Palomar selection and classification policy returned the
recognized advisory result `declined / fuel-exhausted`; its positive and
ill-typed controls passed. This is not con-ron acceptance. The public Palomar
full-preflight workflow and registry review have not been run.

All project paths below are relative to `TranscendentalTuran/`, unless stated
otherwise. The independent target is `Challenge.lean`; it imports only Mathlib.
The final solution imports the proved development and does not import
`Challenge.lean`.

## What the theorem says

An `RGraph (Fin n) 3` is an actual finite set of three-element vertex sets.
`RGraph.IsEmbedding` requires a globally injective vertex function and edge
preservation, including injectivity on isolated vertices. It expresses ordinary
subgraph containment. The extremal number maximizes the edge count over these
actual finite hosts. The definition of `turanDensity` is the infimum of the
binomial-normalized extremal densities for orders at least three;
`TuranUniversality.extremalDensity_tendsto` proves this equals their limit.

The final witness is `Construction.singleGraph`, an explicitly
computable finite graph. Its vertex set and edge enumeration are enormous;
the effective construction is a terminating finite algorithm, not a feasible
plan to print the entire edge list.

The proved transcendental density is

\[
  6\,\Psi\!\left(22-\frac{1024}{15\pi}\right).
\]

The corner Green value itself is not asserted to be a Turán density.
`lambda` is the maximum of the unnormalized cubic edge polynomial;
the factor six converts it to the density normalization.

## The dependency chain

| Manuscript step | Formal interface | Mathematical role |
| --- | --- | --- |
| Actual ordinary finite graphs | `Core/Basic.lean` and `TuranUniversality/Hypergraph/Basic.lean` | Fixes containment and the factor-six normalization. |
| Positive declarations and local rules | `Encoding/` and `Construction/SourceBasis.lean` | Gives a decidable ordinary class and its actual finite forbidden basis. |
| Seventeen violation certificates | `Encoding/Certificates/` | Every local failure has a bounded positive witness with at most forty roots and thirteen data vertices. |
| Four resistors | `Network/PartialIsoSeries.lean`, `StageEnergy.lean`, `ActualReduction.lean` | Proves grounded energy reduction, including missing incidences and incomplete chains. |
| Owner coordinates and incomplete bases | `Network/MarkedComponent.lean`, `MarkedSourceGain.lean` | Constructs the actual projection to the quadrant and controls private leaves. |
| Source-gain upper bound | `Network/RootedSourceGain.lean`, `BlockSourceGain.lean` | Proves the actual corner-Green correction, including the manuscript's six block-mean hypotheses and the marked/unmarked cases. |
| Localize the real maximum | `Construction/MaximizerLocalization.lean`, `LocalizedCoordinates.lean` | Derives the root box, data/root ratio and declaration budget at an actual finite maximum. |
| Eliminate undeclared vertices | `Construction/TypeSurgery*.lean`, `TypeCompletion.lean` | Uses finite induction and a nondecreasing change of the actual edge set. |
| Atomic polynomial | `Construction/TypedPolynomial.lean` | Separates ordinary root/type terms, marker gain and actual layer energy. |
| Exact rational objective | `Optimization/SourceCoefficients.lean`, `SourceObjective.lean` | Identifies those terms with the paper's free-root objective. |
| Source-class upper bound | `Construction/SourceUpper.lean` | Completes partial roots, takes a genuine maximum, localizes, declares all types and applies the bound. |
| Finite realizations | `Green/Realization/` | Builds actual finite typed graphs with the desired energy and type masses. |
| Source-class lower bound | `Green/Realization/ClassLower.lean` | Takes the filler-size limit and the finite-box limit inside the ordinary-class supremum. |
| Exact source value | `Construction/SourceValue.lean` | Combines both inequalities to identify `classLambda` with `Ψ`. |
| A single ordinary forbidden graph | `Construction/SingleGraph.lean` and `Transfer/` | Transfers the source supremum to one actual finite graph via guarded factors and private pair extensions. |
| Corner Green evaluation | `Green/CornerEvaluation.lean`, `CornerTranscendence.lean` | Identifies the walk-defined Green value with `22 - 1024 / (15*pi)`. |
| Arithmetic reduction | `Algebra/` and `Optimization/PaperValue.lean` | Uses real quantifier elimination and a positive parameter coefficient to prove transcendence of the optimized value. |
| Main conclusion | `Main.lean` | Identifies the witness's ordinary density and proves its transcendence. |

## Why the upper bound applies to every legal finite host

The upper argument does not begin with a type-complete graph or prescribed root
weights. A partial rooting is first completed by adjoining missing roots and
adding the permitted root and neutral-pair edges. The vertex embedding preserves
the original polynomial contribution.

On the completed graph the actual finite probability simplex has a maximum.
The complete root clique supplies its baseline value. The weighted Euler
identity in the data direction bounds the total data mass. Actual missing-root
pairs and actual root links yield the root-transfer inequality. Together these
give positive root mass `s`, data mass `t` satisfying `t/s ≤ 2/q`, and the
normalized coordinate bounds `1/q - 16/q² ≤ z_r/s ≤ 1/q + 16/q²`.

Those bounds prove the exact declaration budget. The one-vertex surgery chooses
a type of minimum current declared mass, adds its declaration pairs and removes
the specified incident links. Its legality is proved from all seventeen rules.
Its polynomial gain is nonnegative under the budget already derived from the
maximum. Induction on the number of undeclared vertices terminates.

The atomic polynomial identity and grounded source-gain estimate now apply.
The coefficient bridge identifies their expression with the rational objective.
Finally the cubic homogeneity identity restores the original probability
normalization. This route avoids assuming the desired weight or type conditions
as additional hypotheses on the source class.

## Why the lower bound uses actual finite graphs

The finite-box construction supplies the seven physical types, the four matching
chains and the ownership relations. Legality is checked for the resulting
ordinary edge set. Chain weights are chosen by resistance interpolation, and
their actual layer energy agrees with the finite-network quadratic energy.

For each fixed box, isolated declared vertices fill the difference between its
type masses and the target masses. Distributing each difference among `L`
vertices gives a proved error proportional to `1/L`. First let `L` tend to
infinity. Then let the box size tend to infinity; its corner Green values tend
to the quadrant value.

The actual optimizing point has every type mass greater than `1/(32*q)`.
The total source demand is strictly less than that bound. Consequently the
finite source construction fits within every target type budget, and the two
limits give the lower bound for the exact maximizing objective.

## Effective single-graph construction

`Construction/EffectiveFiniteGraph.lean` supplies finite graph encodings,
decidable pullbacks, pair extensions, products and labels obtained by sorting
encodings. The finite guarded obstruction family is enumerated using the actual
decider for source admissibility and actual ordinary containment of the guard.
Its factors are indexed by their explicit encodings. The final graph is the
categorical product of their private pair extensions, with a computable labeling
by a finite interval.

Equality and embedding lemmas connect these executable operations to the graph
operations used in the ordinary-density transfer. No enormous graph is evaluated
during the proof. The inlining annotations control module initialization and
do not replace a proof by an external computation.

## Recorded proof adaptations

1. The guard is the manuscript's exact disjoint-clique guard. A previously proved
   coarser cubic inequality establishes the required numerical bound.
2. A private extension vertex is added for every core pair, including pairs
   already covered by a core edge. The two properties used in the transfer are
   proved for this convention.
3. The lower approximation uses the complete finite-box Green vector in place
   of the manuscript's finite-walk truncation. Its occupation bound, energy
   identity and convergence give the same limiting value.
4. The guarded basis enumerates all bounded labeled obstructions, avoiding a
   choice of isomorphism representatives. This preserves the finite forbidden
   class and makes the construction effective.
5. Rectangular indexing of diagonal chains includes two additional chains
   with neither base endpoint. Their six private vertices have weight zero;
   legality is checked and their polynomial and energy contributions vanish.
6. Reservoirs have an exact energy cost `C_n / m` for each fixed box `n`.
   The proof takes `m` to infinity before taking the box size to infinity,
   instead of proving the manuscript's coarser uniform-looking displayed
   estimate. It neither interchanges the limits nor assumes a bound on `C_n`
   uniform in the box size.
7. The two-walk determinant identity is proved by its recurrence and boundary
   conditions. The equality to actual finite direction-word and graph-walk
   counts is checked; a separate tail-swapping involution is not required.
8. The Catalan boundary limit uses Mathlib's proved Wallis-product limit and
   an exact product identity, instead of repeating the manuscript's
   sine-integral argument. The telescoping identity and the final Green value
   are unchanged.
9. The four-resistor proof uses weighted composition inequalities for finite
   partial bijections, retaining defects for missing endpoints. This replaces
   the manuscript's separate chain/stub classification and proves the same
   reduced energy. `Network/BlockSourceGain.lean` supplies the source-gain
   statement with the six block-mean hypotheses; the main upper proof uses
   the specialized individual-root interval already derived by localization.

## Verification boundary

The independent Challenge contains one intentional target hole. No solution
module imports it. Proof-development sources use no custom axioms,
`native_decide`, or admitted proof placeholders.

The full source replay, default build and final main-theorem dependency audit
are complete. The audit covers 13 declarations, including `main_result`,
`executable_main_result`, `buildSingleGraph`, the density identity and limit,
both source-class inequalities, and the six-block-mean source-gain theorem.
Every audited declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`; the exact lists are in `verification/axioms.txt`.

Independent statement comparison and external kernel replay are distinct
checks. The first invocation stopped during sandbox setup when `bwrap` was
denied a `NETLINK_ROUTE` socket; its log remains in
`verification/comparator.log`. The subsequent invocation used the documented
isolated compatibility mechanism and passed the independent Challenge/solution
statement and definition comparison, the permitted-axiom check, and both the
Lean default kernel and NanoDa replays. Its original strict configuration also
ran con-ron with default worker settings. That phase exited 137 without a
diagnostic, so the combined command exited 1. This failed invocation is retained
in `verification/comparator-isolated.log` and
`verification/comparator-isolated-exit.json`; it is not reported as a passing
combined command or retroactively classified as a capacity decline.

The fixed Palomar verifier manifest selects the `v4.36.0-rc1` con-ron release
for this Lean source toolchain. Both the release archive and executable matched
the prescribed hashes, as recorded in
`verification/con-ron-selected/download-receipt.json`. The authenticated binary
has the same digest as the locally bundled executable. The independent replay
used exactly `--jobs=2 --verified` on the same protected solution export and
exited 3 with one fuel-exhaustion verdict at
`TranscendentalTuran.Optimization.Paper.A_eval_eq`. The byte-authenticated
official classifier returned `declined / fuel-exhausted`; see
`verification/con-ron-selected/replay.json`.

The selected checker accepted the 466-declaration positive control and rejected
the ill-typed negative control, recorded in
`verification/con-ron-selected/controls.json`. The pinned policy permits this
recognized fuel decline as advisory after mandatory acceptance and successful
controls. It supplies no con-ron acceptance of the solution. The local
`scripts/verify-comparator.sh` now follows the mandatory Lean/NanoDa phase;
`scripts/replay-con-ron.py` performs the separately classified advisory replay.
These local results do not assert completion of the official public pipeline.

The pinned official Palomar full-preflight workflow has not been run. It
requires a public repository and the full 40-character SHA of the reviewed
commit. Passing the pinned metadata validator is a separate contract check.
No public full-verification result, registry acceptance or independent human
mathematical review is claimed.
