import HRS.Main.ThermLinAux8
import HRS.Main.ThermLinAux9
import HRS.Main.ThermLinAux5
import HRS.Main.T25PAux33

/-!
# THERMLIN, part 10 (PLAN 2, SPEC ONLY): the Gaussian comparison `Y` versus `Z_β` without the weak equation of `Y`

**SPEC-ONLY FILE.  Every theorem below is `sorry`; the file is NOT root-imported (do not add it to `HRS.lean`).  It only
records statements that were checked to be well typed (the file compiles) plus the verified plan.**

Goal: `HRS.Main.thermlin_gaussian_comparison` (ThermLinAux5, TeX M L6969-7011).  Replaces the plan of `ThermLinAux6`.

## VERDICT

* The proposed route (test the weak equation of `Y` with `U^β_{r,t}φ`, `Y = W Y⁰ + ∫ W Θ Y + W-convolution`) does NOT work as
  stated, for three checked reasons.
  (R1) `IsLinearFluctuationSolution` (HRS/Dynamics/Setup.lean:234) has NO weak-equation field: its fields are `init`, `cont`,
  `meas` and `gaussian_part` (`Y^t(φ) - Y⁰(U^{0,t}φ)` is a centred Gaussian family independent of `Y⁰`, with the covariance
  `2q∫_0^{t∧t'} μ^r(∇U^{r,t}φ·∇U^{r,t'}ψ)dr`).  `Y` is only known through its finite-dimensional laws, i.e. through
  `T25P.t25p_fdd/t25p_hid/t25p_lin_unique` (T25PAux11:68, T25PAux23:21, T25PAux29:94), which identify its law with that of
  `V^{t,0}X⁰ + Zb`, `Zb = ∫V dG` an `IsStochConv` (Spec.lean:675).  There is nothing to test.
  (R2) The forcing `Θ_r Y^r`, `Θ_r = (𝓛_r-𝓛_β)^T : E_{m-a₀} → E_m`, needs `Y^r ∈ E_{m-a₀}` (`a₀ = aExp d s ∈ [1,2)`), but
  `Y⁰ ∈ L^p(E_m)` only, so `E‖Y^r‖_{E_{m-b}} ≤ C(1+‖Y⁰‖)` is false (infinite) and `Θ_r V^{r,0}Y⁰` is undefined.  The
  initial datum must be split off (zero-start reduction, `tl2_init_shift`, costs `K e^{-ca}‖ν‖_{L^p}` by the decay of `V`),
  and the forcing must sit on the W-convolution `Zw = ∫W dG` of the noise of `Y`, which does lie in `E_{m-a₀}`
  (`tl2_Zw_moment`).
  (R3) The W-outer Dyson identity `V = W + ∫ W Θ V` that the route needs is not available: `duhamel_coeff`
  (MeanFieldAdjointDuhamel:394, instantiated in `thermlin_dyson_coeff`, ThermLinAux9:22) is the FROZEN-OUTSIDE form
  `U^{u,t}φ = U^β_{u,t}φ + ∫_u^t U^β_{u,r}(𝓛_r-𝓛_β)U^{r,t}φ dr`, i.e. `V = W + ∫ V Θ W` for operators.
* Verdict on N1-dual: **NO, it is not avoided**, but it shrinks to a pairing identity for SMOOTH tests (`tl2_dyson_pairing`,
  M-L, ~500 lines): no operator-level identity on `E_m`, no `Θ_r` as an operator, no W-outer form.
* Verdict on N2 (stochastic Fubini for `IsStochConv`): **NO, it is not avoided** in substance (the process-level identity
  `Zs - Zw = ∫ V Θ Zw dr` is a Fubini), but the operator-valued Riemann-sum Fubini (~1500 lines) is REPLACED by a
  second-moment computation (`tl2_cov_mixed` + `tl2_dyson_fubini`, ~650 lines): `D := ⟨Zs^t-Zw^t,φ⟩ - ∫_0^t⟨Zw^r,Δ_rU^{r,t}φ⟩dr`
  satisfies `E D² = ∫ Cd(σ)(a_σ-b_σ,a_σ-b_σ)dσ = 0` by ordinary Fubini of deterministic integrals and `tl2_dyson_pairing`
  (`a_σ = b_σ`).  Only `IsStochConv` second moments (Gaussian fdd of `gfb4_vec_gaussian`, mixed evolutions) are used.
* Total estimate: about **4700 lines** (range 3500-6000) in ~20 lemmas, i.e. NOT shorter than the 4300 of `ThermLinAux6`;
  what changes is the risk profile (no new stochastic-integral theory; every ingredient is an existing lemma or a
  deterministic computation).  The two genuinely new analytic items are `tl2_dyson_pairing` and `tl2_lyapunov`.

## THE ROUTE (V-outer, zero-start; stage 2 with the evolution `W`)

1. Replace `Y` by the canonical process `y ↦ Vev t 0 y + Zs t` on `ν ⊗ P_G` (`tl2_canonical`, `tl2_lin_window_eq` =
   `t25p_lin_unique`; no martingale on the product space is needed).  `Zs = ∫V dG`, `G` Gaussian with `covDensT` along `S.ρ`.
2. Initial datum: `W_p(law window(Vev·y + Zs), law window(Zs)) ≤ K e^{-ca} (∫‖y‖^p dν)^{1/p}` (`tl2_init_shift`, from
   `t25p_rebase_law` T25PAux32:18).  Same lemma for the stationary side with `κ = N(0,C_β)` and `W`.
3. Zero-start comparison with the evolution `W` along the constant path (`thermlin_stationary_traj`, ThermLinAux8:20;
   `t25p_ev_pkg`, T25PAux18:37, is generic in the trajectory, so `T25Ev` for `W` is free: `tl2_Wpkg`).  Apply `t25p_stage2`
   (T25PAux13:44) to `Mart = G`, `Z = Zw = ∫W dG`, `Rr = Zs - Zw`, `Xp = Zs`, `X₀ = X₀' = 0`, `Cb = covDensT m β⁻¹ (const ρβ)`.
   Needed: (a) pathwise `‖Rr^t‖ ≤ C ∫_0^t e^{-c(t-r)}e^{-κ r}‖Zw^r‖_{E_{m-a₀}}dr` (`tl2_remainder_bound` from `tl2_dyson_fubini`,
   `tl2_Delta_bound` = `exists_forwardGen_diff` MeanFieldAdjointLoss:467 and `V`-decay); (b) `sup_r E‖Zw^r‖²_{E_{m-a₀}} ≤ M`
   (`tl2_Zw_moment`; level `m-a₀ > d` because `m > d+2`, `a₀ < 2`); (c) the cost `∫ e^{-2c(a-r)^+}‖covForm ρ^r - covForm ρβ‖_{tr}dr ≤ C e^{-ca}`
   (`tl2_noise_cost`: trace norm ≤ C‖ρ^r-ρβ‖_{L¹} by the `t25p_trace_le_entries` pattern, T25PAux15:54, and `thermlin_rho_decay`,
   ThermLinAux7; rate `e^{-κ r}` not `e^{-2κ r}`: `stage2` wants `traceNormForm (Sg - Cb)`, not Bures); (d) `hid`: the window law of the zero-start
   `W`-Gaussian depends only on `(W,Cb)` (`t25p_Zb_gaussian`, T25PAux9:50, same covariance matrix; `Q54c.toPath_law_eq`).
4. Stationary field: `tl2_stationary_fdd` (fdd of `W ξ + ∫W dĜ` = `stationaryLagCov`, via `tl2_lyapunov`),
   `tl2_stationary_window_indep` (fdd of the window do not depend on `a`; any two stationary fields have the same window law),
   `tl2_zero_start_vs_stationary`.  Assembly `tl2_assembly` = `thermlin_gaussian_comparison` verbatim.

## ANSWERS TO THE FIVE CHECKS (with locations)

(1) Weak equation: none (R1).  The identification of `Y` is by law only.  Testing with `U^β_{r,t}φ` is replaced by the
    deterministic Dyson identity on tests (`tl2_dyson_pairing`), whose regularity is fine: `U^{r,t}φ`, `U^β_{u,r}φ` are smooth
    for smooth `φ` (`Q48e.frozen_smooth`, HRS/Uniform/Q48eAux2.lean:73; `adjkd_propagator_ck2` for the moving coefficient;
    coefficient level `H^j` for every natural `j` in `thermlin_dyson_coeff`), bridges `ClassicalPart.propagator_eq_toFun`,
    `coeffOf_backwardGenerator` (PDE/Classical.lean:217), `propagatorCoeff_shift`.
(2) Aux9-11 with `W`: `t25p_Zb_gaussian` and `t25p_indep_pairing` (T25PAux9) only need a plain evolution with a bound, so they
    run verbatim for `W`; `t25p_cov_eq`/`t25p_fdd` (T25PAux11) take any `IsSmoothPositiveTrajectory`, in particular the
    constant one.  The "extra drift term" is not handled by them (no equation): it is `tl2_dyson_fubini`.
(3) Lyapunov: `tl2_lyapunov` from `PDE.MFLinear.exists_cov_comparison` (MeanFieldLinearLoss:1104; constant trajectory, test
    vector `(f,g)`, `τ = 0`), the projMean decay of Prop 5.2 (`adjoint_decay_comparison`, MeanField.lean ~L236) and time
    homogeneity `Q48e.frozen_semigroup` (Q48eAux2:115) + `Q48e.frozen_smooth`.  `stationaryLagCov` (MeanFieldDefs:113) uses only the
    order and the differences of the `τ_a`, so the fdd of the window of any `IsStationaryGaussianField` (Sec3.lean:47) are independent
    of `a`: `tl2_stationary_window_indep`.  `susceptibilityCov(φ,ψ)` only sees `projMean ψ` (Kernel/Riesz.lean:112-121).
(4) Pathwise bound: on `Zw` (not on `Y`), see R2; `E‖Zw^r‖²_{E_{m-a₀}}` is computed without any operator on `E_{m-a₀}`
    (`tl2_Zw_moment`: diagonal `tl2_cov_mixed` + Hilbert-Schmidt bookkeeping + the dual decay of `W` at level `m-a₀`, A4 at every real
    level).  `p = 1,2` from the `L²` bound (Jensen) and Minkowski in `r`.
(5) Noise term: `tl2_noise_cost`.  Alternative `Q54c.bures2_covForm_le` (Q54cAux37:55) is linear in `sup|ρ^r-ρβ|` but not needed.

## LEMMA TABLE (statement below; size S ≤ 100, M ≤ 400, L ≤ 1000 lines; dependencies in brackets)

| id | name | size | key existing inputs |
|----|------|------|---------------------|
| A1 | `tl2_Wpkg` | S | `t25p_ev_pkg` T25PAux18:37, `thermlin_stationary_traj` ThermLinAux8:20 |
| A2 | `tl2_canonical` | S-M ~150 | refactor of `thermlin_preparedLinear_exists` ThermLinAux4:35 (`Q45.exists_gaussian_martingale`, `adjk_evolution_moment_proof` AdjKAFinal:58) |
| A3 | `tl2_lin_window_eq` | S | `t25p_lin_unique` T25PAux29:94 |
| A4 | `tl2_init_shift` | M ~200 | `t25p_rebase_law` T25PAux32:18, `wassersteinE_le_of_coupling` Prob/Metrics:468 |
| B1 | `tl2_dyson_pairing` | M-L ~500 | `thermlin_dyson_coeff` ThermLinAux9:22, `ClassicalPart.propagator_eq_toFun`, `coeffOf_backwardGenerator` |
| B2 | `tl2_Delta_bound` | M ~300 | `exists_forwardGen_diff` MeanFieldAdjointLoss:467, `exists_pert_path` MeanFieldAdjointDuhamel:863, `thermlin_rho_decay` |
| B3 | `tl2_cov_mixed` | S-M ~150 | `gfb4_vec_gaussian` GFB4Aux4:22 (two integrand families), `t25p_Zb_gaussian` |
| B4 | `tl2_dyson_fubini` [B1,B3] | M-L ~500 | `t25p_cov_eq` T25PAux11:31 (`covForm_lpFun`), `t25p_pullback_eq_lpFun` |
| B5 | `tl2_remainder_bound` [B2,B4] | M ~300 | `V`-decay (`adjk_evolution_along_trajectory`), duality `t25p_memSobolev_of_dual` |
| C1 | `tl2_Zw_moment` [B3] | M ~350 | `thermlin_stationary_evolution` at level `m-a₀` (ThermLinAux8:31) |
| C2 | `tl2_rho_sup_decay` | S-M ~100 | `wire_sup_le` MeanFieldAdjointWiring:61, `thermlin_rho_decay` |
| C3 | `tl2_traceNorm_covForm_diff` | M ~150 | `t25p_trace_le_entries` T25PAux15:54, `t25p_traceNormForm_le_entries` T25PAux14:37, `Q48c.covForm_basis` |
| C4 | `tl2_noise_cost` [C2,C3] | M ~150 | elementary integral |
| D1 | `tl2_xi_law` | S | `thermlin_exists_gauss_kernel` ThermLinAux1:236, Fernique (`IsGaussian.memLp_id`) |
| D2 | `tl2_lyapunov` | L ~500 | `exists_cov_comparison` MeanFieldLinearLoss:1104, `Q40b.q40b_finiteRegHyp` Q40bAux2:22, `Q48b.q48b_mfPath_const` Q48bAux1:108, `Q48e.frozen_*` |
| D3 | `tl2_stationary_fdd` [D1,D2] | M ~400 | `t25p_Zb_gaussian`, `t25p_indep_pairing` T25PAux9:85, `t25p_cov_eq` (const trajectory), `Q48e.frozen_semigroup` |
| D4 | `tl2_stationary_window_indep` | S-M ~150 | `Q54c.toPath_law_eq` Q54cAux1:106, `windowPath_shift` (as in `t25p_hid`) |
| D4' | `tl2_zero_start_law_unique` | M ~120 | `t25p_Zb_gaussian`, `Q54c.toPath_law_eq`, `gfb4_modify` (as in `t25p_hid`) |
| D5 | `tl2_zero_start_vs_stationary` [A4,D3,D4,D4',Z0,xi_law] | M ~250 | product space `ξ ⊗ P_Ĝ`, `tl2_init_shift` |
| E1 | `tl2_zero_start_comparison` [A1,B5,C1,C4,D4',Z1] | M ~300 | `t25p_stage2` T25PAux13:44, `gf_measurable_modification_proof` |
| Z0-Z3 | `tl2_isStationary_finite`, `tl2_CbDens_det`, `tl2_frozen_shift`, `tl2_Vev_decay` | S each, ~215 total | see docstrings |
| E2 | `tl2_assembly` [A3,A4,Z3,E1,D5] | S-M ~150 | `wassersteinE_triangle` Prob/Metrics:414 |

Sum ≈ 4700 lines.  Implementation order: B1, D2, B3 (independent, highest risk / cheapest to de-risk first), then B4, B2, C1, B5, D3-D5, A-lemmas, E.

## DOUBTFUL POINTS (statement-level)

* `tl2_dyson_pairing`: pairs the frozen-evolved `Δ_rU^{r,t}φ` with `z ∈ E_m`; true because both are smooth, but the proof must pass
  from Fourier coefficients (`thermlin_dyson_coeff`, natural `j > d/2+4`) to `H^m` with `j > m`, uniformly in `r ∈ [u,t]`.
* `tl2_Zw_moment`/`tl2_Delta_bound` need `m - a₀ > d` (true: `m > d+2`, `a₀ < 2`) and the real-level decay of `W` (A4 gives all levels).
* `tl2_lyapunov`: relies on the hypotheses of `exists_cov_comparison` (even `j`, `FiniteRegHyp`, `K` large) for the constant trajectory;
  the identification `Mcov = N_u` for the constant path is a rewriting with `mfPath` of the constant coefficient path.
* In `tl2_remainder_bound` the constants `C, κ` depend only on `(S, m)`; `K, c` are the (intrinsic, by `t25p_dual_unique`) decay constants of `Vev`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-! ## Definitions used by the planned statements -/

/-- `U^β_{u,t}`: the frozen adjoint propagator along the constant path `ρβ`. -/
abbrev tl2Ub (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (u t : ℝ) (φ : Torus d → ℝ) : Torus d → ℝ :=
  propagator S.dyn (fun _ => ρβ) u t φ

/-- `Δ_r = 𝓛_r - 𝓛_β`, the difference of the backward generators along `S.ρ` and along the frozen `ρβ`. -/
def tl2Delta (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (r : ℝ) (ψ : Torus d → ℝ) : Torus d → ℝ :=
  fun x => backwardGenerator S.dyn (S.ρ r) ψ x - backwardGenerator S.dyn ρβ ψ x

/-- The `E_{m-b}`-norm of an element of `E_m` (`∞` if it is not in `E_{m-b}`):
`‖z‖²_{E_{m-b}} = ∑_k ⟨k⟩^{2b} coord_k(z)²`. -/
def tl2NormShift (m b : ℝ) (z : NegSobolev d m) : ℝ≥0∞ :=
  (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (2 * b) * NegSobolev.coord z k ^ 2)) ^ (1 / 2 : ℝ)

/-- The stationary covariation density `r ↦ covForm m β⁻¹ (ρβ dx)` on `[0,T']`. -/
abbrev tl2CbDens (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (m T' : ℝ) :
    ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  covDensT m S.β⁻¹ T' (fun _ => ρβ)

/-- Sanity: the two spellings of the dynamics agree. -/
example (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    (thermlin_stationary_traj S h).dyn = S.dyn := rfl

/-- Finite-horizon version of `IsStationaryGaussianField` (Sec3.lean:47): the same three requirements, but only for times in
`[0,T']`.  This is the predicate satisfied by the stationary process `W^{t,0}ξ + ∫_0^t W^{t,r} dĜ_r` built on a finite
horizon (`tl2_stationary_fdd`); every `IsStationaryGaussianField` satisfies it for every `T'`
(`tl2_isStationary_finite`). -/
structure Tl2StatFdd (S : HRS.Main.PreparedData d) (ρβ : Torus d → ℝ) (m T' : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m) : Prop where
  meas : ∀ t, Measurable (Z t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T')
  gaussian : ∀ (p : ℕ) (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ),
    (∀ a, τ a ∈ Set.Icc (0 : ℝ) T') → (∀ a, Torus.IsSmooth (φ a)) →
    law P (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (PDE.stationaryLagCov d S.s S.β (PDE.mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) ρβ τ φ)

/-- (Z0) [XS, ~15 lines] an `IsStationaryGaussianField` is a `Tl2StatFdd` for every horizon (restriction of the
hypotheses from `[0,∞)` to `[0,T']`). -/
theorem tl2_isStationary_finite (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ} (m T' : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m)
    (hZ : IsStationaryGaussianField P S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) : Tl2StatFdd S ρβ m T' P Z := by
  sorry

/-- (Z1) [S, ~60 lines]: the covariation density `tl2CbDens` of the stationary field is a deterministic covariance
density on `[0,T']` and vanishes after `T'` (`t25p_detCov` T25PAux19:19 for `thermlin_stationary_traj`; the second
part is `covDensT` unfolded).  Needed to apply `t25p_stage2` (hypotheses `hCb`, `hCb0`) and `relative_covariance_coupling_proof`. -/
theorem tl2_CbDens_det (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) {T' : ℝ} (hT' : 0 < T') :
    IsDetCovDensity T' (tl2CbDens S ρβ m T') ∧ ∀ r : ℝ, T' < r → tl2CbDens S ρβ m T' r = 0 := by
  sorry

/-- (Z2) [S, ~80 lines]: time homogeneity of the frozen propagator on smooth tests,
`U^β_{u,t} φ = U^β_{0,t-u} φ` for `0 ≤ u ≤ t` (`Q48e.frozen_semigroup`, `propagatorCoeff_shift`; both sides are smooth,
so equality of Fourier coefficients suffices).  Used in `tl2_dyson_pairing` and `tl2_lyapunov`/`tl2_stationary_fdd`. -/
theorem tl2_frozen_shift (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) :
    tl2Ub S ρβ u t φ = tl2Ub S ρβ 0 (t - u) φ := by
  sorry

/-! ## Part A: evolution packages and the canonical (zero-start) linear process -/

/-- (Z3) [S, ~60 lines]: the decay constants of the dual evolution along `S.ρ` are intrinsic: there are `K₀ ≥ 0`, `c₀ > 0`
such that every plain dual evolution `Vev` at level `m` along `S.ρ` satisfies `‖Vev t u‖ ≤ K₀ e^{-c₀(t-u)}` for
`0 ≤ u ≤ t`.  (`adjk_evolution_along_trajectory` gives one such evolution with decay; `t25p_dual_unique` identifies any
other with it on the simplex, because smooth tests include the `realMode`s.)  This makes the constants in `tl2_assembly`
independent of the horizon `a + T`. -/
theorem tl2_Vev_decay (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ K₀ c₀ : ℝ, 0 ≤ K₀ ∧ 0 < c₀ ∧ ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution S.dyn S.ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K₀ * Real.exp (-c₀ * (t - u)) := by
  sorry

/-- A1 [S, `t25p_ev_pkg` applied to `thermlin_stationary_traj`]: the stationary evolution `W` at level `m`, with decay
and, for every window length `T`, the evolution package `T25Ev` (plain, decay, measurable maximal estimate, existence of
continuous measurable stochastic convolutions). -/
theorem tl2_Wpkg (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) :
    ∃ Cw cw : ℝ, 0 < Cw ∧ 0 < cw ∧ ∃ Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution S.dyn (fun _ => ρβ) m Wev ∧
      ∀ T : ℝ, 0 < T → ∃ Cmax : ℝ, 0 ≤ Cmax ∧ T25Ev m Cw cw T Cmax Wev := by
  sorry

/-- A2 [S-M, refactor of the body of `thermlin_preparedLinear_exists`, ThermLinAux4 L35-134]: the canonical data of the
zero-start process: a continuous Gaussian Hilbert martingale `G` with covariation `covDensT` along `S.ρ`, its
stochastic convolution `Zs` against the dual evolution `Vev` along `S.ρ`, and for every initial law `ν` the prepared
linear process `Vev t 0 y + Zs t ω` on `ν ⊗ P_G`.  The decay constants `K, c` of `Vev` are those of the existential in
the conclusion; `tl2_remainder_bound` is applied to exactly this `Vev`. -/
theorem tl2_canonical (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T' : ℝ) (hT' : 0 < T') :
    ∃ (Ωg : Type) (_ : MeasurableSpace Ωg) (Pg : Measure Ωg) (_ : IsProbabilityMeasure Pg)
      (ℱ : Filtration ℝ ‹MeasurableSpace Ωg›) (G Zs : ℝ → Ωg → NegSobolev d m)
      (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      IsDualEvolution S.dyn S.ρ m Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) ∧
      IsHilbertMartingaleWithCovariation Pg ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) ∧
      (∀ ω, Continuous fun s => G s ω) ∧ (∀ ω, G 0 ω = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T',
        IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) ∧
      (∀ t, Measurable (Zs t)) ∧ (∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 T')) ∧
      ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν],
        HRS.Main.IsPreparedLinear S m T' ν (ν.prod Pg) (fun p => p.1) (fun t p => Vev t 0 p.1 + Zs t p.2) := by
  sorry

/-- A3 [S, `t25p_lin_unique`]: every prepared linear process has the window law of the canonical one (same initial
law).  This replaces `Y` by the canonical process `y ↦ Vev t 0 y + Zs t`. -/
theorem tl2_lin_window_eq (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T a : ℝ) (hT : 0 < T)
    (ha : 0 ≤ a) {Ωg : Type} [MeasurableSpace Ωg] (Pg : Measure Ωg) [IsProbabilityMeasure Pg]
    (Zs : ℝ → Ωg → NegSobolev d m) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
    (hcan : HRS.Main.IsPreparedLinear S m (a + T) ν (ν.prod Pg) (fun p => p.1) (fun t p => Vev t 0 p.1 + Zs t p.2))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m)
    (hY : HRS.Main.IsPreparedLinear S m (a + T) ν P' Y₀ Y) :
    law P' (HRS.Main.windowPath m T a Y) =
      law (ν.prod Pg) (HRS.Main.windowPath m T a (fun t p => Vev t 0 p.1 + Zs t p.2)) := by
  sorry

/-- A4 [M, ~200 lines, `t25p_rebase_law` + `wassersteinE_le_of_coupling`]: replacing the initial datum `x ~ κ` by `0`
in a window of `x ↦ U^{a+t,0}x + Z` costs `K e^{-ca} ‖κ‖_{L^p}` (`hc : 0 ≤ c` is needed: `e^{-c(a+t)} ≤ e^{-ca}` for `t ≥ 0`).  Used twice: for `V` and `κ = ν` (initial term of `Y`),
for `W` and `κ = N(0, C_β)` (initial term of the stationary field). -/
theorem tl2_init_shift {m T a K c : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (Uev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Uev (a + T))
    (hdec : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Uev t 0‖ ≤ K * Real.exp (-c * t))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (κ : Measure (NegSobolev d m)) [IsProbabilityMeasure κ] (p : ℝ) (hp : p = 1 ∨ p = 2) :
    wassersteinE p
      (law (P'.prod κ) (Uniform.windowPath a T (fun t (w : Ω' × NegSobolev d m) => Uev t 0 w.2 + Z t w.1)))
      (law P' (Uniform.windowPath a T Z)) ≤
    ENNReal.ofReal (K * Real.exp (-c * a)) * (∫⁻ x, ‖x‖ₑ ^ p ∂κ) ^ (1 / p) := by
  sorry

/-! ## Part B: the Dyson identity at the level of tests, and the Fubini identity by a variance computation -/

/-- B1 [M-L, ~500 lines]: the V-outer (frozen-outside) Dyson identity paired with `z ∈ E_m`, for smooth tests:
`⟨z, U^{u,t}φ⟩ = ⟨z, U^β_{u,t}φ⟩ + ∫_u^t ⟨z, U^β_{u,r}(𝓛_r - 𝓛_β)U^{r,t}φ⟩ dr`.  From `thermlin_dyson_coeff`
(ThermLinAux9, coefficient level, natural `j > d/2+4`; take `j > m`) by (i) `ClassicalPart.propagator_eq_toFun`,
`coeffOf_backwardGenerator` (`forwardGen ↔ backwardGenerator`), `propagatorCoeff_shift` (time homogeneity of the frozen
part) to turn coefficients into functions, and (ii) summing over `k` against the coefficients of `z`, interchanging the
sum and the `dr`-integral by dominated convergence (the integrand is continuous in `r` in `H^m`). -/
theorem tl2_dyson_pairing (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (z : NegSobolev d m) :
    NegSobolev.eval z (propagator S.dyn S.ρ u t φ) =
      NegSobolev.eval z (tl2Ub S ρβ u t φ) +
        ∫ r in u..t, NegSobolev.eval z
          (tl2Ub S ρβ u r (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) := by
  sorry

/-- B2 [M, ~300 lines]: `P:eq:Gaussian-forcing` on tests, from `PDE.MFAdjoint.exists_forwardGen_diff`
(MeanFieldAdjointLoss L467, `i = m`, `r > d/2 + m` from `thermlin_rho_decay`) and `exists_pert_path` (MeanFieldAdjointDuhamel
L863): `‖(𝓛_r - 𝓛_β)ψ‖_{H^{m-a₀}} ≤ C e^{-κ r} ‖ψ‖_{H^m}`, `a₀ = aExp d s ∈ [1,2)`, so `m - a₀ > d`. -/
theorem tl2_Delta_bound (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ r : ℝ, 0 ≤ r → ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      MemSobolev (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ∧
      sobolevNorm (m - PDE.MFAdjoint.aExp d S.s) (tl2Delta S ρβ r ψ) ≤ C * Real.exp (-κ * r) * sobolevNorm m ψ := by
  sorry

/-- B3 [S-M, ~150 lines, `gfb4_vec_gaussian` with `p = 2` and two different integrand families]: the cross second moment
of two stochastic convolutions of the SAME martingale against two plain evolutions (the single-evolution case is
`t25p_Zb_gaussian`). -/
theorem tl2_cov_mixed {m T K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hT0 : 0 < T)
    (V₁ V₂ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hV₁c : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V₁ p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hV₂c : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V₂ p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hV₁b : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V₁ t r‖ ≤ K₁)
    (hV₂b : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V₂ t r‖ ≤ K₂)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m) (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Z₁ Z₂ : ℝ → Ω → NegSobolev d m)
    (hZ₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V₁ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Z₁ t))
    (hZ₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V₂ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Z₂ t))
    (hZ₁m : ∀ t, Measurable (Z₁ t)) (hZ₂m : ∀ t, Measurable (Z₂ t))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T)
    {φ₁ φ₂ : Torus d → ℝ} (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Z₁ t₁ ω) φ₁ * NegSobolev.eval (Z₂ t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V₁) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData V₂) t₂ σ (gfb4_ell m φ₂)) := by
  sorry

/-- B4 [M-L, ~500 lines]: THE REPLACEMENT OF THE STOCHASTIC FUBINI (N2).  With the same Gaussian martingale `G`
(covariation `covDensT` along `S.ρ`), `Zs = ∫V dG` and `Zw = ∫W dG`, for each smooth test and each `t`, almost surely
`⟨Zs^t - Zw^t, φ⟩ = ∫_0^t ⟨Zw^r, (𝓛_r - 𝓛_β)U^{r,t}φ⟩ dr`.
Proof: `D := LHS - RHS` is a centered square-integrable variable; `E D² = 0`.  By `tl2_cov_mixed` (pairs `(Zs,Zw)`,
`(Zw,Zw)`), `t25p_cov_eq`-type bookkeeping and ORDINARY Fubini on `[0,t]²×[0,t]` for the deterministic integrands
`σ ↦ Cd σ (b_σ, b'_σ)`, `E D² = ∫_0^t Cd(σ)(a_σ - b_σ, a_σ - b_σ) dσ` with `a_σ = lpFun(U^{σ,t}φ - U^β_{σ,t}φ)` and
`b_σ = ∫_σ^t lpFun(U^β_{σ,r}Δ_rU^{r,t}φ) dr`; `a_σ = b_σ` is `tl2_dyson_pairing` (an equality in `H^m`, by testing with
the coordinate functionals).  No stochastic integral is interchanged with an ordinary one. -/
theorem tl2_dyson_fubini (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' : ℝ} (hT' : 0 < T') {K : ℝ} (hK : 0 ≤ K)
    (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVd : IsDualEvolution S.dyn S.ρ m Vev) (hVp : IsPlainEvolution Vev T')
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev) (hWp : IsPlainEvolution Wev T')
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zs Zw : ℝ → Ω → NegSobolev d m)
    (hZs : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t))
    (hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t))
    (hZsm : ∀ t, Measurable (Zs t)) (hZwm : ∀ t, Measurable (Zw t))
    (hZwc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T'))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ =
      ∫ r in (0 : ℝ)..t, NegSobolev.eval (Zw r ω)
        (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := by
  sorry

/-- B5 [M, ~300 lines]: the pathwise bound of the remainder `R = Zs - Zw`, simultaneously for all `t ∈ [0,T']`.
For each of countably many rational combinations `φ` of Fourier modes (norm in `E_m` = supremum over them) use B4, then
`|⟨z, ψ⟩| ≤ ‖z‖_{E_{m-a₀}} ‖ψ‖_{H^{m-a₀}}`, B2 for `ψ = U^{r,t}φ - mean` (constants are killed by `Δ_r`) and the dual decay
`‖U^{r,t}φ - mean‖_{H^m} ≤ K e^{-c(t-r)} ‖φ‖_{H^m}` (= decay of `Vev` on `E_m`); continuity in `t` of `Zs - Zw`
extends rational `t` to all `t`.  `C, κ` depend on `(S, m)` only; `K, c` are the decay constants of `Vev`. -/
theorem tl2_remainder_bound (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ {T' : ℝ}, 0 < T' → ∀ {K c : ℝ}, 0 ≤ K → 0 < c →
      ∀ (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn S.ρ m Vev → IsPlainEvolution Vev T' →
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T' → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) →
        IsDualEvolution S.dyn (fun _ => ρβ) m Wev → IsPlainEvolution Wev T' →
        (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K) →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
        (G : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
      ∀ (Zs Zw : ℝ → Ω → NegSobolev d m),
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t)) →
        (∀ t, Measurable (Zs t)) → (∀ t, Measurable (Zw t)) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 T')) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T')) →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T',
          ‖Zs t ω - Zw t ω‖ₑ ≤ ENNReal.ofReal (C * K) *
            ∫⁻ r in Set.Icc (0 : ℝ) t,
              ENNReal.ofReal (Real.exp (-c * (t - r)) * Real.exp (-κ * r)) *
                tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) := by
  sorry

/-! ## Part C: moments of `Zw` at level `m - a₀`, and the noise-covariation cost -/

/-- C1 [M, ~350 lines] (`P:eq:Gaussian-forcing` second half, the `N3` of ThermLinAux6): `sup_{r ≤ T'} E ‖Zw^r‖²_{E_{m-a₀}} ≤ M`
with `M` independent of `T'`.  No operator on `E_{m-a₀}` is needed: by `tl2_cov_mixed` (diagonal case),
`E ‖Zw^r‖²_{E_{m-a₀}} = ∑_k ⟨k⟩^{2a₀-2m} ∫_0^r 2β⁻¹ ∫ ρ^σ |∇U^β_{σ,r} ψ_k|² dσ`, and
`∑_k ⟨k⟩^{-2m'} ‖U^β_{σ,r}ψ_k‖²_{H¹} ≤ ‖U^β‖²_{H^{m'}→H^{m'}} ∑_k ⟨k⟩^{2-2m'} ≤ C e^{-2c(r-σ)}` for `m' = m - a₀ > d`
(dual decay of `W` at level `m'`, `thermlin_stationary_evolution S h m'`; `∑ ⟨k⟩^{2-2m'} < ∞` since `2m'-2 > d`). -/
theorem tl2_Zw_moment (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {T' : ℝ}, 0 < T' →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn (fun _ => ρβ) m Wev → IsPlainEvolution Wev T' →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
        (G : ℝ → Ω → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
      ∀ (Zw : ℝ → Ω → NegSobolev d m),
        (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t)) →
        (∀ t, Measurable (Zw t)) →
        ∀ r ∈ Set.Icc (0 : ℝ) T', ∫⁻ ω, tl2NormShift m (PDE.MFAdjoint.aExp d S.s) (Zw r ω) ^ 2 ∂P ≤ ENNReal.ofReal M := by
  sorry

/-- C2 [S-M, ~100 lines] (sup norm from `H^r`, `wire_sup_le` MeanFieldAdjointWiring L61, and `thermlin_rho_decay`):
`|ρ^r(x) - ρβ(x)| ≤ C e^{-κ r}`. -/
theorem tl2_rho_sup_decay (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : Torus d, |S.ρ r x - ρβ x| ≤ C * Real.exp (-κ * r) := by
  sorry

/-- C3 [M, ~150 lines]: the trace norm of a difference of covariation forms is bounded by the `L¹` distance of the
densities (pattern: `T25P.t25p_trace_le_entries`, `t25p_entry_abs_le`, `Q48c.covForm_basis`; the entries are
`2q w_k w_l ∫ F_{kl} d(μ₁ - μ₂)` with `|F_{kl}| ≤ 2d⟨k⟩⟨l⟩`, and `∑ w_k⟨k⟩ < ∞` for `m > d+1`). -/
theorem tl2_traceNorm_covForm_diff (m : ℝ) (hm : (d : ℝ) + 2 < m) (q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ₁ ρ₂ : Torus d → ℝ, Continuous ρ₁ → Continuous ρ₂ → IsProbDensity ρ₁ → IsProbDensity ρ₂ →
      traceNormForm (covForm m q (withDensityReal ρ₁) - covForm m q (withDensityReal ρ₂)) ≤
        C * ∫ x, |ρ₁ x - ρ₂ x| := by
  sorry

/-- C4 [M, ~150 lines]: the noise cost term of `t25p_stage2` (rate `e^{-κ r}`, not `e^{-2κ r}`: trace norm instead of
Bures; harmless). -/
theorem tl2_noise_cost (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) ^ 2 *
        traceNormForm (covDensT m S.β⁻¹ (a + T) S.ρ r - tl2CbDens S ρβ m (a + T) r)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) := by
  sorry

/-! ## Part D: the stationary field -/

/-- D1 [S, `thermlin_exists_gauss_kernel` (ThermLinAux1 L236) + Fernique]: the initial law `N(0, C_β)` of the stationary
field, with finite moments. -/
theorem tl2_xi_law (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ γ : Measure (NegSobolev d m), IsProbabilityMeasure γ ∧
      IsCenteredGaussianWithCov m γ (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β) ∧
      (∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂γ) < ⊤ := by
  sorry

/-- D2 [L, ~500 lines] THE LYAPUNOV IDENTITY (`C:eq:stationary-cov`).  Two limits, no differentiation of the semigroup:
(i) `PDE.MFLinear.exists_cov_comparison` (MeanFieldLinearLoss L1104) for the constant trajectory of
`thermlin_stationary_traj` (`FiniteRegHyp` from `Q40b.q40b_finiteRegHyp`, `mfPath` of the constant coefficient path
`Q48b.q48b_mfPath_const`) and the test vector `(f, g)`, `τ = 0`: `N_u(f,g) → stationaryLagCov(0)(f,g) = C_β(f, projMean g)`;
(ii) decay `C_β(U_u f, U_u g) → 0` (`PDE.adjoint_decay_comparison`, projMean part: the first bullet of Prop 5.2);
(iii) splitting `N_{t+u}(f,g) = N_t(f,g) + N_u(U_t f, U_t g)` (time homogeneity, `Q48e.frozen_semigroup`,
`Q48e.frozen_smooth` so that `U_t f` is again an admissible smooth test) and letting `u → ∞`.
`C_β(f,g) = C_β(f, projMean g)` is the definition (`responseInverse` only sees `projMean g`). -/
theorem tl2_lyapunov (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) {f g : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) {t : ℝ} (ht : 0 ≤ t) :
    susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β f g =
      susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β (tl2Ub S ρβ 0 t f) (tl2Ub S ρβ 0 t g) +
        2 * S.β⁻¹ * ∫ σ in Set.Icc 0 t, ∫ x,
          inner ℝ (Torus.grad (tl2Ub S ρβ 0 σ f) x) (Torus.grad (tl2Ub S ρβ 0 σ g) x) * ρβ x := by
  sorry

/-- D3 [M, ~400 lines]: the finite-dimensional laws of `Z̃^t = W^{t,0} ξ + ∫_0^t W^{t,r} dĜ_r` (`ξ ~ N(0,C_β)` independent of
a Gaussian martingale `Ĝ` with covariation `covForm ρβ`) are `multivariateGaussian 0 stationaryLagCov`.  Proof: the sum of
the independent pieces (`t25p_indep_pairing`, `t25p_Zb_gaussian`, `t25p_cov_eq` for the constant trajectory) has covariance
`C_β(U_t φ, U_s ψ) + 2β⁻¹∫_0^{t∧s}⟨ρβ∇U_{t-σ}φ,∇U_{s-σ}ψ⟩dσ`; for `t ≤ s`, with `U_{s-σ} = U_{t-σ}U_{s-t}`
(`Q48e.frozen_semigroup`) and `tl2_lyapunov` for `(f,g) = (φ, U_{s-t}ψ)` this is `C_β(φ, U_{s-t}ψ) = stationaryLagCov`. -/
theorem tl2_stationary_fdd (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' K : ℝ} (hT' : 0 < T') (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev) (hWp : IsPlainEvolution Wev T')
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω₃ : Type} [mΩ₃ : MeasurableSpace Ω₃] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃] {ℱ₃ : Filtration ℝ mΩ₃}
    (γ : Measure (NegSobolev d m))
    (hγ : IsCenteredGaussianWithCov m γ (susceptibilityCov (periodicRiesz d S.s) (withDensityReal ρβ) S.β))
    (ξ : Ω₃ → NegSobolev d m) (hξ : Measurable ξ) (hξlaw : P₃.map ξ = γ)
    (Ĝ : ℝ → Ω₃ → NegSobolev d m)
    (hĜ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ T' Ĝ (fun r _ => tl2CbDens S ρβ m T' r))
    (hĜc : ∀ ω, Continuous fun s => Ĝ s ω) (hĜz : ∀ ω, Ĝ 0 ω = 0)
    (hind : Indep (MeasurableSpace.comap ξ inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T', MeasurableSpace.comap (Ĝ τ) inferInstance) P₃)
    (Zb : ℝ → Ω₃ → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P₃ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T') →
      (∀ a, Torus.IsSmooth (φ a)) →
      P₃.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Wev (ts a) 0 (ξ ω) + Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (PDE.stationaryLagCov d S.s S.β S.dyn ρβ ts φ) := by
  sorry

/-- D4 [S-M, ~150 lines]: the window law of a finite-horizon stationary Gaussian field does not depend on the position
`a` of the window, and two such fields have the same window law.  Only the finite-dimensional laws on `[0,a+T]` (resp.
`[0,T]`) enter: the matrix `stationaryLagCov` involves only the order and the differences of the times `τ_a`.  Proof:
`Q54c.toPath_law_eq` on the windows (the fdd of `Z₁` at times `a+t_i` equal those of `Z₂` at times `t_i`, both being
`multivariateGaussian 0 (stationaryLagCov …)` with the same matrix) and `windowPath_shift`/`toPath_eq_windowPath`, exactly as
in `t25p_hid` (T25PAux23:21-93).  Finite horizon is essential: the field built by `tl2_stationary_fdd` lives on `[0,a+T]`
only.  Via `tl2_isStationary_finite` it applies to any `IsStationaryGaussianField`. -/
theorem tl2_stationary_window_indep (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ} (m T : ℝ) (hT : 0 < T)
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (Z₁ : ℝ → Ω₁ → NegSobolev d m) (Z₂ : ℝ → Ω₂ → NegSobolev d m)
    {a : ℝ} (ha : 0 ≤ a)
    (hZ₁ : Tl2StatFdd S ρβ m (a + T) P₁ Z₁) (hZ₂ : Tl2StatFdd S ρβ m T P₂ Z₂) :
    law P₁ (HRS.Main.windowPath m T a Z₁) = law P₂ (HRS.Main.windowPath m T 0 Z₂) := by
  sorry

/-- D4' [S-M, ~120 lines] (the `hid` hypothesis of `t25p_stage2` for the zero-start Gaussian target): the window law of a
zero-start `W`-stochastic convolution `Zb = ∫ W dĜ` depends only on `(W, Cb)`, not on the probability space or on the
martingale `Ĝ`.  Proof: `t25p_Zb_gaussian` (T25PAux9:50) gives the fdd as `multivariateGaussian 0` of a matrix determined by
`(W, Cb)`, for test functions in `MemSobolev m`; then `Q54c.toPath_law_eq` as in `t25p_hid` (the coordinates `coord k`
are the pairings with `realMode k`, smooth by `q48b_isSmooth_realMode`).  The martingales are only assumed to satisfy `IsHilbertMartingaleWithCovariation` (this is what the call sites in
`t25p_stage2`'s `hid`, D5 and E1 provide); the proof first replaces each `Ĝ` by a continuous modification vanishing at `0`
(`gfb4_modify`, which needs `hCb0`; `gfb4_isStochConv_congr`), exactly as in `t25p_hid` (T25PAux23:54-62).  `tl2CbDens`
satisfies `hCb0` (zero off `[0,a+T]` by definition of `covDensT`).  Both processes need continuity a.e. on `[0,a+T]`
and measurability.  Note that the initial datum plays no role here: the stationary side of `tl2_zero_start_vs_stationary`
adds `W ξ`, and `tl2_init_shift` removes it. -/
theorem tl2_zero_start_law_unique {m T a K : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Wev (a + T))
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Wev t r‖ ≤ K)
    (Cb : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    {Ω₂ Ω₃ : Type} [mΩ₂ : MeasurableSpace Ω₂] [mΩ₃ : MeasurableSpace Ω₃]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] (P₃ : Measure Ω₃) [IsProbabilityMeasure P₃]
    {ℱ₂ : Filtration ℝ mΩ₂} {ℱ₃ : Filtration ℝ mΩ₃} (Ĝ₂ Zb₂ : ℝ → Ω₂ → NegSobolev d m) (Ĝ₃ Zb₃ : ℝ → Ω₃ → NegSobolev d m)
    (hĜ₂ : IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ₂ (fun r _ => Cb r))
    (hĜ₃ : IsHilbertMartingaleWithCovariation P₃ ℱ₃ (a + T) Ĝ₃ (fun r _ => Cb r))
    (hCb0 : ∀ σ : ℝ, σ ∉ Set.Icc 0 (a + T) → Cb σ = 0)
    (hZ₂ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ₂ 0 t (Zb₂ t))
    (hZ₃ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P₃ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ₃ 0 t (Zb₃ t))
    (hm₂ : ∀ t, Measurable (Zb₂ t)) (hm₃ : ∀ t, Measurable (Zb₃ t))
    (hc₂ : ∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb₂ t ω) (Set.Icc 0 (a + T)))
    (hc₃ : ∀ᵐ ω ∂P₃, ContinuousOn (fun t => Zb₃ t ω) (Set.Icc 0 (a + T))) :
    law P₂ (Uniform.windowPath a T Zb₂) = law P₃ (Uniform.windowPath a T Zb₃) := by
  sorry

/-- D5 [M, ~250 lines] (the `hid` of `t25p_stage2` for the zero-start Gaussian target): the window law of
`Zb = ∫W dĜ` (zero initial datum) depends only on `(W, Cb)`, by `t25p_Zb_gaussian` (same covariance matrix) and
`Q54c.toPath_law_eq`; and the window at `a` of the stationary field `W ξ + Zb` is the stationary window law.  Combined with
`tl2_zero_start_law_unique` (to pass from the given `(Ω₂, Ĝ, Zb)` to a product-space system `ξ ⊗ Ĝ'` with `ξ ~ N(0,C_β)`
from `tl2_xi_law`), `tl2_init_shift` (`κ = N(0,C_β)`, to add the initial term `W ξ`), `tl2_stationary_fdd` (the process
`Z̃ = W ξ + Zb'` has the stationary fdd on `[0,a+T]`; it is measurable and a.e. continuous on `[0,a+T]` because `Wev · 0 x`
is continuous by `IsPlainEvolution` and `Zb'` is), hence `Tl2StatFdd S ρβ m (a+T)`, and `tl2_stationary_window_indep` with
`tl2_isStationary_finite` for the given `Z`, this gives the `W_p` distance between the zero-start window law and the law of
the window of any `IsStationaryGaussianField`.  The constants `C, c` come from the decay of `Wev` (`tl2_Wpkg`, intrinsic to
`Wev` by `t25p_dual_unique`) and `∫⁻ ‖x‖ₑ^p ∂N(0,C_β) < ∞` (`tl2_xi_law`). -/
theorem tl2_zero_start_vs_stationary (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ (p : ℝ), (p = 1 ∨ p = 2) →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m), IsDualEvolution S.dyn (fun _ => ρβ) m Wev →
      (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Wev T') →
      ∀ {Ω₂ : Type} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ mΩ₂}
        (Ĝ Zb : ℝ → Ω₂ → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ (fun r _ => tl2CbDens S ρβ m (a + T) r) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t)) →
        (∀ t, Measurable (Zb t)) → (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE p (law P₂ (Uniform.windowPath a T Zb)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) := by
  sorry

/-! ## Part E: the zero-start comparison (application of `t25p_stage2` with the evolution `W`) and the assembly -/

/-- E1 [M, ~300 lines]: `t25p_stage2` for the evolution `W` (`T25Ev` from `tl2_Wpkg`), `X₀ = X₀' = 0`, `Mart = G`
(`Sg = covDensT` along `S.ρ`), `Cb = tl2CbDens`, `Z = Zw` (from `T25Ev.exists_conv` + `gf_measurable_modification_proof`),
`Rr = Zs - Zw`, `Xp = Zs`, `Bm = ofReal C * ∫⁻_{[0,a+T]} ofReal(e^{-c max(a-r,0)} e^{-κ r}) * tl2NormShift (Zw r)`
(`tl2_remainder_bound`, with `∫_{[0,t]} ≤ ∫_{[0,a+T]}` for `t ≤ a+T` by monotonicity of the integrand sup),
`E Bm^p` by Minkowski + `tl2_Zw_moment` + `∫_0^{a+T} e^{-c max(a-r,0)} e^{-κ r} dr ≤ C e^{-c'a}`, noise cost `tl2_noise_cost`
(Cauchy-Schwarz exponent 1/2 absorbed in `c`), and `hid` from `tl2_zero_start_law_unique` (D4'; `X₀' = 0` forces `ξ = 0` a.s., so `Wev t 0 (ξ ω) = 0` a.s. and `Λ` is the window law of `Zb`).  Output: the
zero-start process `Zs` of the linear equation is `C e^{-ca}`-close in `W_p` to ANY zero-start `W`-Gaussian with
covariation `Cb`. -/
theorem tl2_zero_start_comparison (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a → ∀ (p : ℝ), (p = 1 ∨ p = 2) →
      ∀ {Ωg : Type} [mΩg : MeasurableSpace Ωg] (Pg : Measure Ωg) [IsProbabilityMeasure Pg] {ℱ : Filtration ℝ mΩg}
        (G Zs : ℝ → Ωg → NegSobolev d m) (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
        IsDualEvolution S.dyn S.ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
        IsHilbertMartingaleWithCovariation Pg ℱ (a + T) G (fun r _ => covDensT m S.β⁻¹ (a + T) S.ρ r) →
        (∀ ω, Continuous fun s => G s ω) → (∀ ω, G 0 ω = 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)) →
        (∀ t, Measurable (Zs t)) → (∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zs t ω) (Set.Icc 0 (a + T))) →
      ∀ (Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m), IsDualEvolution S.dyn (fun _ => ρβ) m Wev →
      (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Wev T') →
      ∀ {Ω₂ : Type} [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂] {ℱ₂ : Filtration ℝ mΩ₂}
        (Ĝ Zb : ℝ → Ω₂ → NegSobolev d m),
        IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) Ĝ (fun r _ => tl2CbDens S ρβ m (a + T) r) →
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Ĝ 0 t (Zb t)) →
        (∀ t, Measurable (Zb t)) → (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
        wassersteinE p (law Pg (Uniform.windowPath a T Zs)) (law P₂ (Uniform.windowPath a T Zb)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) := by
  sorry

/-- E2 [M, ~150 lines]: assembly.  `W_p(law Y^{a+·}, law Z^{a+·}) ≤ W_p(Y, Ycan_{ν}) + W_p(Ycan_ν, Ycan_{δ₀}) ...`:
by `tl2_lin_window_eq`, `Y` is replaced by the canonical process; `tl2_init_shift` (with `V`, `κ = ν`) compares it with the
zero-start `Zs`; `tl2_zero_start_comparison` compares `Zs` with a zero-start `W`-Gaussian (constructed once with
`Q45.exists_gaussian_martingale` and `T25Ev.exists_conv`); `tl2_zero_start_vs_stationary` compares that with the stationary
field; `wassersteinE_triangle`.  The statement is `thermlin_gaussian_comparison` (ThermLinAux5) verbatim.
Bookkeeping: (i) `tl2_canonical` lives on `ν.prod Pg` (datum first) whereas `tl2_init_shift` is stated on `P'.prod κ` (noise
first); one `Measure.prod_swap` step identifies the two laws.  (ii) The constants must not depend on `a`, although
`tl2_canonical` is applied with horizon `a + T`: take the decay constants of `Vev` from `tl2_Vev_decay` below, not from the
existential of `tl2_canonical`, and use `K = max (K_V) (K_W)` where `tl2_remainder_bound` wants a common constant.  (iii) The
zero-start `W`-system `(Ĝ, Zb)` is constructed once per `a` (`Q45.exists_gaussian_martingale`, `T25Ev.exists_conv`,
`gf_measurable_modification_proof`) and the same system is passed to `tl2_zero_start_comparison` and
`tl2_zero_start_vs_stationary`.  (iv) The final constants are `c = min` and `C = max` of the constants of the four terms
(`C > 0` so that `ofReal (C e^{-ca}) ≠ 0` and no `0 * ⊤` occurs). -/
theorem tl2_assembly (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
        {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        HRS.Main.IsPreparedLinear S m (a + T) ν P' Y₀ Y →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 1 (law P' (HRS.Main.windowPath m T a Y)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) * (1 + ∫⁻ y, ‖y‖ₑ ∂ν) ∧
        wassersteinE 2 (law P' (HRS.Main.windowPath m T a Y)) (law P'' (HRS.Main.windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) *
            (1 + (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) := by
  sorry

end HRS.ThermLin.Plan2
