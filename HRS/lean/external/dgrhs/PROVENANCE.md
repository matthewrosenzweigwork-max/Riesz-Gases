# Vendored DGRHS-Lean modules

Vendored copies of the transitive import closure of `DGRHS.Attractive.SourceUniform` and
`DGRHS.CLT.SourceRawEnergy` from the author's repository `dgrhs-lean`
(commit `0865a0a`, directory
`proof/`), Lean v4.34.1, Mathlib d13f23b (the same pins as this project).

They supply the generic uniform partition-function bound for the attractive logarithmic
interaction under factorial row moments (Delgadino-Gvalani-Rosenzweig, Theorem 2.6 and
Remark 2.1), used by `HRS/Equilibrium/PreparationAttractive.lean`.
Checked there: `DGRHS.Attractive.source_uniform_partition` depends only on
`propext, Classical.choice, Quot.sound`.

## Addition 2026-10-16 (upstream commit `5de9754`)

Upstream sources (upstream `proof/DGRHS/...`; Mathlib-only closure; the 239 earlier source files were byte-identical across these two upstream revisions at
`5de9754`):
`DGRHS.Original.SourcePathTightness`, `DGRHS.Original.SourcePathContinuousPaths` (tight + fdd convergence ⇒ weak
convergence of path laws, incl. `C([0,T],E)`), `DGRHS.Entropy.GibbsEntropyRewrite`, `DGRHS.Entropy.GibbsFiniteDomain`,
`DGRHS.Entropy.GibbsExtendedRewrite` (EReal Gibbs relative-entropy rewrite for exponents bounded above).
Checked (private compile, default autoImplicit): `sourceContinuousPath_tendsto_of_isTight`, `sourcePath_law_eq_of_fdd_eq`,
`sourcePath_tendsto_of_isTight_of_fdd`, `sourcePath_tendsto_of_isTight_of_gaussian_fdd`, `sourcePath_tendsto_of_isTight_polish`,
`gibbsEntropy_rewrite`, `gibbsExtendedFreeEnergy_rewrite`, `gibbsKL_finite_domain` depend only on
`propext, Classical.choice, Quot.sound`. Intended users: path-law convergence (A.11 `main_torus_path`, Sec5
`dynamic_convergence`, `ui_qualitative`) and the B.15 packet-A0 Gibbs bridges.

## Public source preparation

Only comments in `DGRHS/Original/SourcePathTightness.lean` and
`DGRHS/Original/SourcePathContinuousPaths.lean` were edited for the release copy.
Their Lean code is unchanged. All other vendored Lean source files are unchanged.
