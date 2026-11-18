import HRS.Main.TorusTheorems

/-!
# Packet A1014 (Corollary A.10 `torus_field_wasserstein`, Corollary A.14 `true_limit_stat`,
`true_limit_stat_base`, `true_limit_field`): statement check and proof plan

TeX: `M:B:cor:torus-field-wasserstein` (L10351-10378, proof L11398-11434), `M:B:cor:true-limit`
(L10409-10435, no proof printed; the proof is "A.8 / A.9 plus Proposition A.34").
No declaration of this file; it records the statement check (2026-10-17) and the plan.

## 1. Statement check (SPEC-C0B-repaired statements)

### `torus_field_wasserstein` (A.10): TRUE AS WRITTEN (no defect found)
* Quantifier order as in A.9 (`∃ C₀min` after `(s)`, `∃ C ΛT` before the data, `C ≤ N` with `C > 0`
  forced `≥ 2` in the proof); `N ≥ 1` (`C ≤ N`, `0 < C`) so no `N = 0` junk.
* Junk values.  `wassersteinE` is an `iInf` over couplings in `ℝ≥0∞` (value `⊤` if there is no coupling, which only
  happens if a law is not a probability measure); it is compared with `ENNReal.ofReal(finite)`, so the statement
  asserts existence of a coupling.  Both laws are probability measures: `ηF N` is measurable
  (`InitialFluctuationField.ηF_meas`), `particleFieldLaw` is the push-forward of a measurable map
  (`a9_Z_meas`, uses the filtered solution in `TorusStanding`), `νG` is a probability measure
  (`IsLinearFieldNoise.1`), so the `Measure.map` junk value `0` does not occur.  `ofReal` of the right-hand side:
  `masterRate ≥ 0` (`εf ≥ 0`, `σ ≥ 0`, `q ≥ 0`, `𝔈 > 0`, `𝔈' ≥ 0`, `N ≥ 0`), so no clipping of a negative argument;
  `rpow` bases `𝔈, N` are positive.  Bochner integrals do not occur (all moments are `lintegral`s).
* Degenerate parameters.  `MainData d` carries `1 ≤ d`, `0 ≤ s < d`, `T > 0`; for `s ∉ [0,d)` no `MainData` exists
  (the statement is vacuous there and `C₀min` is arbitrary).  `t = 0` allowed (then the bound is
  `C [εf + ...]`, still true: `Z^0 = 𝕀^0` and `Ĩ + G^0` with `G^0 = 0`; the proof treats all `t ∈ [0,T]` alike).
* Hypotheses are satisfiable and not contradictory: `A.9` (same hypotheses, W₁ replaced by `d_{C²}`) is proved as
  stated, `ε2` appears only inside `EnergySmallness2` (its `I1_L2` is vacuous for the empty family),
  the `W₂` clause adds `0 ≤ εf2` and the `L²` initial coupling `∫⁻ ‖κΞ⁰ - ηF‖² ≤ ofReal(εf2²)`; both measures have
  finite second moment in the relevant sense, but the statement is a coupling-cost bound (no moment is needed).
* Match with the TeX.  `masterRate d εf q σ 𝔈 𝔈 N = εf + √q(𝔈^{1/4} + N^{-1/(2d)}) + σ𝔈` is exactly
  `B:eq:torus-field-w1` (`q = σ²/(Nβ)`); with `(εf2, 𝔈')` it is `B:eq:torus-field-w2` (the first-moment `𝔈` stays inside
  `√q 𝔈^{1/4}`, as in the TeX: the covariance error `D_N^t` uses `𝔈`, not `𝔈'`).  `A_N κ_N = σ_N` makes the
  initial term `𝕀 - Ĩ = A_N V^{t,0}(κΞ⁰ - η°)`, bounded by the uniform bound of `V^{t,0}` on `E_γ`.
* The TeX proof uses the Hilbert-space Itô representation of the modewise martingale field and the trace-norm
  bound for `D_N^t` (`B:eq:torus-field-trace-error`).  The repository has no `E_γ`-valued Itô integral for the
  particle martingale (see the GF-PM remark in `GFAux1`); the plan below replaces it by finite-mode projections.

### `true_limit_stat` (A.14, statistics, quantitative): TRUE AS WRITTEN
* Same quantifier order as A.8 (`C ΛT` before `m₀`), so the constant coming from A.34(i) (which depends on
  `m₀`) must be made uniform over the finitely many `m₀ ∈ [1, m_*]` (`InitialFluctuation.m₀_pos/m₀_le`); this is
  bookkeeping, not a defect (the A.34 bound is linear in its constant).
* `A.34(i)` is applied with `m = m_*`, `η = (R N).η`, `FunctionalMoment` obtained from `I2`/`linear`/`η_meas`
  (each of the two summands of `I2` is `≤` the sum), `m_* ≤ m + 2` trivial.
* `W₁(fluct, surrogate_∞) ≤ W₁(fluct, surrogate_N) + W₁(surrogate_N, surrogate_∞)`.  The triangle inequality
  needs the three laws to be probability measures: `surrogateStatLaw` is (convolution of the law of a measurable
  vector with a Gaussian), `fluctStatLaw` is because `W₁(fluct, surrogate_N) < ⊤` by A.8 (a coupling exists, hence
  the first marginal has mass 1): no junk value.  The bound `‖φ‖_{m_*} ≤ ‖φ‖_{m_*+2}` is not needed.
* `Δ_N := coeffDiscrepancy ≥ 0` is a sum of absolute values and an `iSup` of norms over a compact interval
  (`a34_delta_facts`), so `Δ + √Δ` has no junk value.  `φ ∈ H^{m_*+2}` implies `φ ∈ H^{m_*}`
  (`memSobolev_mono_idx`).  Conclusion of A.8 and A.34 are summed into one `ofReal`, using that all terms are `≥ 0`
  (`masterRate ≥ 0`, `sobolevNorm ≥ 0`, `Δ ≥ 0`) and `e^{ΛT t} ≥ 1`, with `ΛT := max(ΛT₈, ΛT₃₄)`.

### `true_limit_stat_base` (A.14, base regularity, qualitative): TRUE AS WRITTEN
* `∃ C₀min` only (no `N ≥ C`): the limit statement.  `W₁(fluct, surr_∞) ≤ W₁(fluct, surr_N) + W₁(surr_N, surr_∞)`
  for `N ≥ C` (A.8(a) with the rate `→ 0` of `main_torus_stat_tendsto_proof`, clause 1, and the finite constants
  `C ΛT` of `main_torus_stat_proof`), and the second term `→ 0` by `surrogate_to_limit_stat_base` (proved in place,
  `a34_base_main`) with `m = m_*`.  `m₀ ≤ m_*` is `InitialFluctuation.m₀_le`.

### `true_limit_field` (A.14, fields, quantitative): TRUE AS WRITTEN
* The hypothesis on the transported initial fields compares `Law(A_N V_N ηF_N)` (law under `(R N).P`) with
  `Law_{νin}(A V_∞ F)`; with `law (R N).P (ηF N) = νin` (`InitialFluctuationField.law_eq`) this is the TeX hypothesis
  `B:eq:initial-limit-stability`.  Chain:
  `d₂(particle, limit) ≤ d₂(particle, lin_{ηF}) + d₂(lin_{ηF}, limit)`; the first term is A.9
  (`main_torus_field_proof`); `lin_{ηF} = Law(Ĩ) ∗ νG`, `limit = Law_{νin}(A V_∞ F) ∗ νGlim`, hence
  `d₂ ≤ d₂(Law Ĩ, Law_{νin}(A V_∞ ·)) + d₂(νG, νGlim) ≤ Cs Δ + c (Δ + √Δ)`,
  by `a34_smoothDist_conv`, the hypothesis, and the Gaussian coupling `a34_gauss_couple` (+ `a34_smoothDist_coupling`).
  (`surrogate_to_limit_field` itself is not applicable: its hypothesis is for `Law_{νin}(A_N V_N ·)`, not for
  `Law(ηF_N)` composed; but `law (R N).P (ηF N) = νin` shows it is the same thing, so the pieces are reused.)
* `smoothDist` junk: `smoothDist = ⨆ Φ : CbUnitBall, |...|` is a real `iSup` (junk `0` if unbounded above); on
  finite measures it is bounded (`|∫Φ| ≤ ‖Φ‖_∞ μ(univ)`), and the triangle inequality `smoothDist_triangle` is for
  finite measures.  All four laws are probability measures (see A.10).  `fieldRate ≥ 0`.
* `Cs` may be negative: then the hypothesis forces nothing absurd (it is a hypothesis), and the proof uses `|Cs|`.

## 1b. Notes found while proving
* In this Mathlib pin `Measure.map f μ` of a non-AEMeasurable `f` is a Dirac measure (instance
  `IsProbabilityMeasure (map f μ)` holds for every `f`), not `0`; all maps here are measurable anyway.
* STATUS (2026-10-17): all four statements proved as written (A1014Aux2-11, A1014Final; axioms standard).

## 2. Proof plan

### A.14 (assembly of proved results): `A1014Aux2`/`A1014Final`
(S) `true_limit_stat`: `main_torus_stat_proof` (a) + `a34_stat_main` (uniform over `m₀ ≤ m_*`) + W₁ triangle.
(B) `true_limit_stat_base`: A.8(a) + `main_torus_stat_tendsto_proof` + `a34_base_main` + W₁ triangle.
(F) `true_limit_field`: `main_torus_field_proof` + hypothesis + `a34_gauss_couple`.

### A.10 (the new part): finite-mode projections instead of the `E_γ`-valued Itô integral
Fix `N ≥ 2`, `t ∈ [0,T]`, a finite injective family of modes `k : Fin q → ℤ^d∖{0}` (as in A.9, `a9_core_Phi`),
`T = a9TE`, `ι = embedCLM b` (isometric), `Z = a9Z`, `𝕀 = a9I`, `Ĩ = a9Itil`.
(W1) `a1014_wass_abstract`: `a8p_wass_abstract` with `M : ℝ^q`-valued (polar coupling in `ℝ^q`), `X, Xt, Z` with values in
     the full `E_γ`, `Z = X + ιM_t + R` a.e.: for `p ∈ [1,2]`
     `W_p(Law Z, Law Xt ∗ νG) ≤ ‖Z - X - ιM‖_p + √(covDiscrepancy) + ‖X - Xt‖_p + ‖y - ι c y‖_{L^p(νG)}`
     (four-term chain exactly as `a9_chain`, with `a8p_wass_conv_le`, `wassersteinE_le_of_coupling`,
     `hilbert_polar_coupling`, and `νG.map c = N(0, ∫Σ̄)`).
(W2) `a1014_core`: instantiate with the A.9 objects (`a8p_hilbert_mart`, `a8p_phiH_isHS`, `a8p_sb_isDet`, `a8p_cov_cost_gen`,
     `a9_gauss_law`, `a9_I_diff`, `a9_gauss_tail`, per-mode `a9_rem_moment`, `a9_ZI_moment`): `p = 1` gives the A.9 `ℓ¹`-mode
     bounds; `p = 2` needs the `L²` versions (`a8p_rem_L2`, `E M_j² ≤ 2qT(Ca K_j)²`, `E G_j² ≤ …`) and Minkowski in `L²`
     for the `ℓ¹` mode sums, with `𝔈'` in the remainder and `εf2` in the initial term.
(W3) Arithmetic: `√cost` with `cost ≤ C q (𝔈^{1/2} + N^{-1/d})` gives `√q (𝔈^{1/4} + N^{-1/(2d)})`
     (`a8p_fourth_sq`, `a9_cost_le`, `a9_smear_le`), tails `→ 0` along `E ↑` (`a9_exists_finite_tail`).
(W4) Final: `C := ...`, `ΛT := 1`, `e^{ΛT t} ≥ 1`.
-/

noncomputable section

namespace HRS.Main.A1014

end HRS.Main.A1014
