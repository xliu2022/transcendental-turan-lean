# Contributing

This repository contains the complete formalization of a finite three-graph
with transcendental ordinary Turán density. Start with `README.md` and
`docs/PROOF_MAP.md` for its mathematical interfaces and recorded verification.

1. Keep the proof development in the libraries exported by `Solution.lean`.
   Do not introduce proof holes, custom axioms or `native_decide` dependencies.
2. Keep `Challenge.lean` a small independent statement importing only permitted
   dependencies. Its intentional target hole is separate from the proved
   Solution. Update `comparator.json` if the compared interface changes.
3. Keep `formalization.yaml`, source attribution and licence notices accurate.
   Run `bash verify.sh --checks-only` and `ruby test/validate_formalization_test.rb`
   for the source and metadata checks.
4. Keep Lean and dependency revisions pinned. If changing dependencies, update
   and commit both the root and `docbuild/` manifests, then rerun verification.
5. Run `bash verify.sh`; on a compatible Linux host, also run
   `bash verify.sh --comparator`. Preserve historical evidence in `verification/`
   and write new results to new paths. A changed proof requires fresh evidence;
   do not update the archived source hashes without the corresponding checks.
6. Before a Palomar submission, push the reviewed snapshot, run the configured
   full preflight and use the full 40-character public commit SHA. Preflight,
   editorial review and registration are separate steps.

The following module-system guidance is adapted from the pinned Palomar
template identified in `provenance/Palomar.json`.

## Module system and file sizes

Every regular `.lean` source file in the submitted repository must use Lean's
module system and contain at most **10,000 physical lines**. This includes
Challenge, Solution, unused source files, generated certificates, contained
projects, and local path dependencies. Ordinary comments may precede the
`module` header; module documentation belongs after it. Blank and comment lines
count. LF and CRLF each delimit one line; an unterminated final line counts,
and a final newline does not add an empty line.

Lake configuration files named `lakefile.lean` are exempt from the module
header requirement, but still have the 10,000-line cap. Files below `.git` or
`.lake` are excluded; submitted `.lean` symbolic links are rejected so a link
cannot hide an oversized source file. Separately declared
substantive source repositories for thin wrappers receive the same checks.
External pinned Git dependencies are outside this per-file limit; Lean still
checks their compatibility with the module system. The existing Challenge
limits of **1,000 lines and 100 KiB** also apply.

Porting requires more than adding `module`: make the declarations needed by
other modules public, use `public import` where the public interface needs an
import, and expose definitions whose bodies clients need. See
[Lean's modules and visibility reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#modules-and-visibility).
Rebuild and rerun Comparator after porting. Split oversized files into smaller
modules or reduce generated certificates; do not hide them in excluded paths.

The submission form and HTTPS intake check a bounded subset of the submitted
repository at the exact commit and report incomplete scans explicitly. They do
not scan separately declared substantive repositories; preparation checks those. The verifier scans the complete
checkout before builds and confirms headers with Lean's parser before running
submitted Lake code. Violations identify the file and require a corrected new
commit. These rules apply to new ordinary submissions and revisions; metadata
corrections retain their registered source and are not retroactively rejected.

Run `python3 scripts/check-lean-sources.py` before `lake build`. CI repeats this
non-executing check before installing dependencies or building. The supplied
modules use public imports and declarations; keep this structure as you add
files. This local check complements the full Palomar reusable workflow.
