> Current source differs by one admitted-declaration removal. See [current-source scope](CURRENT_SOURCE_CHANGES.md). The evidence below describes the historical release.

# Scope, evidence and qualifications

## What the evidence is
* "Comparator pass" means: the same statement as an independent Challenge built from the pinned reference head (`4f1238aeec35b6da2fe8941cdbb9fec9837b9134`), checked by the nanoda kernel and the Lean default kernel, with only the axioms `propext`, `Classical.choice`, `Quot.sound`. It is internal verification, not external acceptance.
* Current claim table: `MANIFEST/claims_current.tsv` (the frozen `claims_manifest.tsv` plus its one superseding row in `claims_manifest_changes_repaired.tsv`) (1,182 claim-token rows). Tier-B theorems 1,473/1,473 have Comparator passes; the final theorem (`whole_space_edgeworth`) and 8 headline statements depend only on the standard axioms; `leanchecker --fresh` kernel replays cover the final-theorem closure (10,916 modules) and the headline closure (10,917 modules).
* Retained: 10,922 HRS modules + 244 DGRHS modules. Removed from the source tree before release: 413 HRS modules that no retained module imports (`MANIFEST/deleted_modules.tsv`, with hashes and reasons; 45 contain `sorry`). No declaration inside a retained module was edited by the removal.
* Source hashes: `MANIFEST/SHA256SUMS_included_files.txt` (every file in this package). These hashes describe the sanitized release copy, excluding the checksum file itself. Prior verification receipts apply to the adopted source; the only Lean source edits made for this export are comments/docstrings in 48 files. The Lean toolchain, package pins, declarations and proof code were not edited.

## The one proof change relative to the earlier frozen source
`HRS/Energy/FeatureMap.lean`: only the `sorry` body of `HRS.isSpectralSymbol_negSpectralCoeff` was filled (`MANIFEST/witness_repair_REL_T02.patch`; theorem statements byte-identical). Before the change, `energy_identity_negSpectral` could not pass Comparator (its type mentioned the `sorry` witness; recorded failure, exit 1, `sorryAx`). After: Comparator pass (both kernels), seven related FeatureMap ties pass, final-theorem `leanchecker --fresh` replay passes, and a from-scratch build of this source set succeeded (exit 0, 20,085 jobs, 11,162 compiler runs, none refused). The ~48 earlier Comparator receipts and the headline-closure replay were NOT re-run on the repaired source; their applicability rests on constant-level facts (the witness's reverse closure is 2 constants; no statement hash changed). The cause of 8 value-hash differences inside `HRS.Energy.FeatureMap` is not characterized.

The statement label `HRS.energy_identity_negSpectral` is not the proved provider: the implementation establishing that claim is `HRS.MH.FeatureMap.energy_identity_negSpectral_proof`. The claim ledger preserves historical verification receipt identifiers. The repair patch and the repaired-source hash record describe the pre-sanitization stage, not the present file hashes. The public claim index applies the repaired PASS to the claim, not to any placeholder declaration.

## Proof exclusions (not claimed proved)
* `fdl_commutator`: no proof exists; claim status "stated".
* Old `sorry`-dependent constants flagged earlier (e.g. the unprimed `*_proof` predecessors of `dynamic_entropy_proof'`, `dynamic_comparison_proof'`, `moving_log_moment_proof'`, `moving_pair_moments_proof'`, `Sec7.alltime_Lp_proof'`, `commutator_coercivity_common_proof`, `sde_entropy_law_proof`, `prepared_full_bounds_proof`) remain `sorry`-dependent in the source. The corresponding claims are carried by the clean providers recorded in `claims_manifest.tsv`.
* Five headline definitions in `HRS/Whole/HeadlineStatement.lean` (`quadraticGradientDyn`, `iN`, `jN`, `IsResultingSolution`, `cubicFormula`) have tower and replay coverage only; no independent head-text Comparator Challenge exists for them. Eleven definitions have level-1 (tower-only) coverage; four have partial level-2 coverage.
* Many source files in `HRS/` still contain `sorry` outside the claimed closure statements; presence of a module does not imply it is part of a claim.

## Qualifications on the verification tools
1. Comparator/exporter runs used a read-only-write-denied, network-blocked sandbox, but reads and execution were not confined to an allowlist.
2. The nanoda binary is the installed v4.35.0 release; upstream hash could not be checked offline. The Lean default kernel independently accepted every target.
3. System libc6/libgcc were not pinned; libc6 changed from 2.39-0ubuntu8.9 to 8.12 (security update) partway through the runs (35 of 48 receipts before, 12 after, 1 straddling). The final-theorem export is byte-identical under both.
4. Tool sources declare Lean 4.34.0 while 4.34.1 was used; the lean/lake/leanchecker binaries are byte-identical, the library delta is unused by the checkers.
5. Exporter equivalence (hand-built vs Lake-built) was shown byte-identical on three targets, not all.
Remedies (narrower sandbox, offline-impossible hash fetch, rebuilds against 4.34.1, re-runs) were not performed.

## Not a claim
Not a claim of external review, journal acceptance, or completeness relative to any manuscript; manuscript sources are not included.
