# HRS Lean formalization (Lean-only source package)

Lean 4 sources (`HRS/`, `HRS.lean`) and the vendored DGRHS modules (`external/dgrhs/`, see `external/dgrhs/PROVENANCE.md`).

* Toolchain: `lean-toolchain` = `leanprover/lean4:v4.34.1`; Mathlib `v4.34.1` (commit d13f23b723b8a846827a245b89c10fc7d3f11612), pinned in `lake-manifest.json`.
* Build: `lake exe cache get` (optional, needs network) then `lake build HRS DGRHS`. The historical from-scratch build before the [current-source change](CURRENT_SOURCE_CHANGES.md) took ~14 h on the verification host (20,085 jobs). Memory-hungry: do not run several heavy builds in parallel.
* Helpers kept: `tools/closure.py` (import closure of given modules), `tools/stmtcheck.py` (checks that a file keeps every non-`sorry` line of its spec, in order).
* Start with [Scope and evidence](SCOPE_AND_EVIDENCE.md) for what is proved, conditional or excluded. [Current claim table](MANIFEST/claims_current.tsv) lists retained claims. The original claim ledger and repair are preserved under `MANIFEST/`; the checksum inventory binds current files.
* This package is a source export. It is not a statement of external acceptance, and it was not published by its preparers.

### A first theorem

[Whole-space Edgeworth expansion (supplement S2.1(iii))](HRS/MS/Fp81S21WholeSpaceEdgeworth.lean#L45) is formalized as `HRS.Whole.whole_space_edgeworth`. Its data include a resulting solution satisfying `IsResultingSolution`; the theorem does not assert that such a solution always exists.
