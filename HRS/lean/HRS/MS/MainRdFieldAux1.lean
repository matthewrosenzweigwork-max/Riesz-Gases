import HRS.MP.RdRemainder

/-!
# S.A.6 `main_rd_field` and S.A.7 `rd_field_wasserstein_one/_two`: statement check, plan, and the Lambda-normalisation

Worker SA6.  Namespace `HRS.MS.MainRdField`, helpers `sa6_`.  Frozen rows: `HRS.Whole.AppendixA.main_rd_field`,
`rd_field_wasserstein_one`, `rd_field_wasserstein_two` (`HRS/Whole/AppendixA.lean` L1026-1120), with the M3 hypothesis
`FieldAdjointInputRd fd S Kad`.  TeX: supplement L9915-9981 (theorem, corollary), proofs L10590-10665, lemma
`B:lem:adjoint-field-kernel` L10562-10588, `B:lem:test-cutoff` L10506-10517; main paper L10600-10700 (Hilbert CLT, polar
coupling, assembly).

## 1. Statement check (2026-10-24): one INSUFFICIENCY, everything else true and non-vacuous

**(S1, INSUFFICIENT, second conjunct of `main_rd_field` only, case `fd = decSub (lower _)`).**  The clause
`∃ B, ∀ N ≥ 1, ∀ Ξ representing σ_NΞ_N^t, E‖Ξ‖_{H^{-Γ}} ≤ B` is proved in the TeX "from the same decomposition":
`E‖σΞ‖ ≤ E‖I_emp‖ + E‖M‖ + E‖R‖` with `E‖I_emp‖ ≤ C_in`, `E‖M‖² ≤ 2 q_N d T K_ker² ≤ 2dTK_ker²` (`q_N ≤ 1`), and
`E‖R‖ ≤ C σ_N T (𝔈_N + e_N)`.  `σ_N𝔈_N → 0` is a hypothesis (`EnergySmallnessRd.small`), but `σ_N e_N` is not: for the
lower-regularity density `e_N = (1 + 1_{s=0} log N) N^{-2/((s+1)(s+2))}` and `σ_N` is arbitrary (`σ_N = min(κ_N, √(Nβ_N))`,
`β_N = ∞` allowed), e.g. `d = 3`, `s = 0.8`, `σ_N = N^{0.5}`: `σ𝔈 → 0` is compatible with `𝔈_N ≈ N^{s/d-1} = N^{-0.73}`
(this is the lower bound `𝔈_N ≥ c N^{s/d-1}` forced by the completion), while `σ_N e_N = N^{0.5-0.40} → ∞`.  Nothing in
`fd.Holds` (`HoldsAt (decSub _) = s' < d-2`), `RdStanding`, `TransportedInitialFieldRd`, `FieldAdjointInputRd` bounds
`σ_N e_N` (S.A.25 `path_remainder_rd` takes `Tendsto (σ(𝔈+e)) → 0` as an explicit hypothesis; `main_rd_field` does not).  The
remainder estimate `|Comm| ≤ CK‖φ‖(F + o + e)` of S.B.5(iii) is the only bound on `R` available for the lower density, so
the uniform first-moment bound cannot be derived; the other three cases (`nd`, `decSuperIso`, `decSuperHilb`, and
`decSub (sharp _)`) have `e_N = 0` and are fine.  The first conjunct (existence of `Ξ`; the `d_{C²}` bound, whose right side
contains `σ_N(𝔈_N + e_N)` explicitly) and both Wasserstein corollaries are NOT affected.  Smallest repair (pending review):
add to `main_rd_field` the hypothesis `Tendsto (fun N => S.sigma N * fd.eN N) atTop (𝓝 0)` (or `BddAbove (Set.range _)`),
exactly as in S.A.25 (`B:eq:rd-path-smallness`), or restrict the last conjunct to `fd` not of the form `decSub (lower _)`.
This worker does not edit frozen statements.

**(S2, handled, no statement change).**  `main_rd_field` has no hypothesis `1 ≤ Λ` (the commutator and coercivity inputs
need `Λ ≥ 1`, `B5` has `hΛ : 1 ≤ Λ`); `Λ < 1` is not excluded by `RdStanding` (`cb + weighted sup ≤ Λ` can be `< 1` for a
probability density in `d = 2`).  Fix inside the proof (this file): `sa6_standing_normalise` replaces `(Λ, C₀)` by
`(Λ' = max Λ 1, C₀' = sa6_C0norm ..)` with `oNΛ d s C₀' Λ' N = oNΛ d s C₀ Λ N` for all `N ≥ 1` (an equality), so
`correctedEnergyRd` and hence `EnergySmallnessRd` are literally unchanged; `C₀min` of the theorem is chosen so that
`C₀' ≥` (coercivity threshold `C₀'` of `whole_coercivity_pair`, completion constants of S.B.5(i)-(iii)); this uses that
`∃ C₀min` comes AFTER `Λ` in the statement.  `0 < Λ` follows from `RdStanding` (`sa6_pos_of_standing`).

**(S3, checked true / non-vacuous).**  (a) `C, ΛT` are chosen after `C₀`, before `S`: `ΛT := 1` works (the constants do not
grow with `t`), `C` depends on `d, s, fd, MB, Λ, ΛV, G₀, νbar, T, Cin, m20, χ, Kad, C₀` only (kernel constant of S.A.20,
Lipschitz constant `d·MB·K_ad`, S.B.5 constants, `wN`-constant of `test_cutoff`).  (b) Junk-value traps: `Ξ`-existence needs
`|φ(x)| ≤ K‖φ‖_{H^Γ}`, which is the `deriv` clause at `r = t`, `l = 0` (`propagatorW C t t φ = φ`: `IsClassicalAdjointW.terminal`);
`HNeg.pairing` of smooth tests determines the element (`hneg_eq_zero_of_pairing_zero`, Parseval system `mrm_e`); the
Bochner integrals in `noiseCovW`, `pair`, `commN`, `flucInteractionRd` are not junk (bounded integrands against probability
densities; `CommIntegrableW` from S.B.5); `eLpNorm` / `Measure.map`: all maps used are measurable (`Ξ` by hypothesis, `Iemp`,
`I` by `TransportedInitialFieldRd.meas`); `toReal` of `⊤`: `cNormE χ h < ⊤` is part of S.A.20(4) (`≤ ofReal C`);
`Real.log 0`: only through `Λ > 0` (above) and `oNΛ` at `N ≥ 1`.  `d ≥ 1` (`S.hd`).  `ν_N = 0` (`invβ = 0`): `M ≡ 0`,
`sb ≡ 0`, `νG = δ_0` (centered Gaussian with zero covariance), consistent; `A_N κ_N = σ_N` also at `invβ = 0`
(`Ascale = 1`, `sigmaScale = κ`).  All four regimes and `s = 0` are inside the hypothesis `FieldAdjointInputRd`.  (c) The
representation `IsFluctFieldRepr` is a.s. for each test, and a measurable representative is a.s. unique
(`mrm_ae_eq_of_pairings`), so `law Ξ` does not depend on the representative.  (d) `Iemp`, `I` need not be `ℱ_0`-measurable:
the proof replaces `Iemp` by its a.s. equal `σ(X₀)`-measurable version and uses `I` only through its law (convolution
contraction `HRS.A34.a34_smoothDist_conv`, `HRS.T25.t25_smoothDist_conv_le`).  (e) W-versions: `E‖R‖` (resp. `(E‖R‖²)^{1/2}`
under `EnergySmallness2Rd`) enters with `σ_N(𝔈_N + e_N)` (resp. `σ_N(𝔈'_N + e_N)`), no boundedness needed.

## 2. Plan (packets, each ≤ 2k lines; existing names checked with `grep`)

Common inputs (merged): `HRS.MP.RdMart.{mrm_hilbert_version, mrmZ, mrmPhi, mrm_meas_grad, mrm_measurable_of_pairings,
mrm_ae_eq_of_pairings, mrm_e_parseval, mrm_pairing_*}` (`HRS/MP/RdMartingale.lean`), `HRS.MP.RdProp.rpk_exists_rep`
(`RdPropKernel`), `HRS.MP.HNegInfra.{hneg_norming, hneg_parseval, hneg_norm_le_of_pairing, hneg_eq_zero_of_pairing_zero}`,
`HRS.MH.DualityRd.duality_identity_rd_proof` (frozen `duality_identity_rd`), `HRS.MS.GenPath.s56_fluc_eq_comm`
(`flucInteractionRd = ½ commN`), `HRS.MP.RdRem.{mrr_path_bound, mrr_perN pattern, mrr_coll_ae, mrr_time_moment,
mrr_energy_meas}`, `HRS.Whole.AppendixALemmas.{adjoint_field_kernel (= HRS.MS.SuppU3.adjoint_field_kernel_proof),
test_cutoff_pathwise, test_cutoff_expectation}`, `HRS.MH.CoercTest.p_assembly` (= `whole_coercivity_pair`),
`HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof` and
`HRS.Commutator.Whole.whole_commutator_sub_{sharp,lower}_of_subcoulomb` (S.B.5), `HRS.MS.SuppU15.u15_logmoment`,
`HRS.MS.Go.{s55_grad_lip_cb, s55_oN_mono}` (pattern of `general_orbits_commutator_proof`),
`HRS.hilbert_martingale_clt_cond`, `HRS.hilbert_polar_coupling`, `HRS.hilbert_wasserstein_assembly_{w1,w2}`,
`HRS.A34.a34_smoothDist_conv`, `HRS.T25.t25_smoothDist_conv_le`, `HRS.cbUnitBall_translate`, `HRS.smoothDist_triangle`.
Genuinely missing: B5 (statement-only, unproved, in `HRS/MH/AdjointInputBridge.lean`), the index-`Γ` kernel family without the
increment bound, the `H`-valued decomposition `σΞ = I_emp + M + R` at one time, the covariance form `sb`, the shift lemma
for an `ℱ_0`-measurable `H`-valued `X`, the S.A.7 measure-level assembly.

* **P1 (this file, ~250 lines, DONE below)**: Lambda-normalisation (S2): `sa6_oN_normalise`, `sa6_isRegularMF_mono`,
  `sa6_pos_of_standing`, `sa6_standing_normalise`.
* **P2 `MainRdFieldAux2` (~700): B5 `selectedCommutatorInput_of_adjoint`** (for `Λ ≥ 1`, then S2).  `v = Mᵀ∇U^{r,t}φ` has
  `HasLipBoundW v (d·MB·Kad‖φ‖)` from `deriv` at `l = 2 ≤ m_*` (pattern `s55_grad_lip_cb`, `ContDiff 2` from `ContDiff j`,
  `mStar ≥ 2`); `nd`, `decSuperIso`, `decSuperHilb` (`d-2 ≤ s`): `whole_commutator_super`; `decSub (sharp a)`:
  `whole_commutator_sub_sharp_of_subcoulomb` with `wbound` (shape `HasFracTransportBound (a/2) (2d/(a-2))`);
  `decSub (lower)`: `…_lower_…` and `commLowRateError = fd.eN`; log moment from the weighted bound (`u15_logmoment`),
  `ρ ≤ Λ` from `cbNorm`; constants `K' = max(1,C)·max(1,C)·d·MB·Kad`; `C₀min`.
* **P3 `MainRdFieldAux3` (~500): kernel family at index `Γ`**: for `N ≥ 1`, `0 ≤ r ≤ t ≤ T`, `x`, `j`: `Kern j r t x ∈ H^{-Γ}` with
  `pairing φ (Kern) = ∂_jU^{r,t}φ(x)`, `‖Kern‖ ≤ Kad'` (as `rpk_kernel` with `Γ` instead of `Γ+2`, no increment bound), joint
  measurability in `(r,x)` through pairings (`mrm_measurable_of_pairings`, `mrm_meas_grad`: the classical solution has
  continuous gradient, so the P9 clause `meas` is not needed at a fixed `t`); Dirac representative `δ_x` and the particle
  field `Ξ` (existence conjunct: `rpk_exists_rep` pointwise in `ζ`, measurability by pairings; `E‖Ξ‖` bounds; uniqueness
  a.e. by `mrm_ae_eq_of_pairings`).
* **P4 `MainRdFieldAux4` (~800): the decomposition at fixed `t` (N ≥ 2)**: `Z r ζ (i,j) = c_N·1_{r ≤ t}·Kern j r t (X_r ζ i)`
  (`mrmZ`, `c_N = σ_N√(2β_N⁻¹)/N`), `M := mrm_hilbert_version` (continuous `ℱ`-martingale, `IsHilbertMartingaleWithCovariation`
  with `Σ_r = hsCovForm (Z r ω)`); `I_emp' := Riesz element of φ ↦ σ(⟨U^{0,t}φ,μ_N^0⟩ - ⟨U^{0,t}φ,μ°⟩)` (`σ(X₀)`-measurable,
  a.s. equal to `Iemp N t`, `A_Nκ_N = σ_N`); `R := σΞ - I_emp' - M_t`; a.s. pairing identities from `duality_identity_rd_proof`
  (`f r = propagatorW (S.coeff N) r t φ`, `IsClassicalAdjointW` from `deriv`, `datum`, `s56_fluc_eq_comm`, `gradComp ↔
  partialDeriv`, `itoIntegral` linearity in the constant); `E‖R‖ ≤ ½ K' σ T (𝔈+e)` and `(E‖R‖²)^{1/2} ≤ ½ K' σ T (𝔈'+e)`
  (copy of `mrr_perN` at the index `Γ`, time `t` fixed, via the countable norming family and `Z`-integral, using
  `mrr_coll_ae` from the occupation clause of the flow, so no fixed-time collision-freeness is needed).
* **P5 `MainRdFieldAux5` (~700): covariance**: `sb σ x y := 2q_N ∫ Σ_j ⟨Kern j σ t z,x⟩⟨Kern j σ t z,y⟩ ρ_σ(z) dz`
  as an element of `H →L[ℝ] H →L[ℝ] ℝ`, `IsDetCovDensity t sb` (measurability from P3, `IsTraceClassCov` from the
  Parseval/HS-sum, `traceNormForm` integrable); `IsGaussianWithIntegratedCov t sb νG` from `IsLinearFieldNoiseRd`
  (agreement of the covariance forms on the dense span of Riesz representatives of smooth tests, both continuous);
  `E ∫_0^t ‖Σ_r - sb_r‖_{S₁} dr ≤ C q_N w_N`: `Σ_r - sb_r = 2q ∫ Σ_j Kern⊗Kern d(μ_N - μ_β)`, trace norm = `sup_B ⟨h_{B,r}, μ_N - μ_β⟩`
  with `B` self-adjoint after symmetrisation, `cNormE χ h_B ≤ C` (S.A.20(4)), the PATHWISE `test_cutoff_pathwise` (uniform in `h`
  up to `𝒩(h)`, so the sup is inside), then the `Q09A.lintegral_bound` optimisation of `test_cutoff_expectation` (copy with the
  trace-norm functional in place of one pairing; `wN` appears through `inf_bound`).
* **P6 `MainRdFieldAux6` (~600): `d_{C²}` assembly (S.A.6)**: `Φ ∈ CbUnitBall H 2`; (1) `|EΦ(σΞ) - EΦ(I_emp'+M_t)| ≤ E‖R‖`
  (`norm_sub_le_of_mem_one`); (2) shift lemma: for `X` `ℱ_0`-measurable `H`-valued,
  `|EΦ(X+M_t) - E f_Φ(X)| ≤ ½ D`, `f_Φ(x) = ∫Φ(x+z)dνG` (countable `𝒢`-valued approximation of `X` + `hilbert_martingale_clt_cond`
  for `Φ(x_k + ·)`, `cbUnitBall_translate`); (3) `f_Φ ∈ CbUnitBall` is not needed: use `t25_smoothDist_conv_le` on laws
  (`Law(X)∗νG` vs `Law(I)∗νG`); (4) `ΛT := 1`, constants, `N ≥ C` threshold, `C₀min`; the existence conjunct from P3.
* **P7 `MainRdFieldAux7` (~250): first moment** (given the repaired hypothesis (S1) for `decSub (lower)`; unconditionally for the
  other three cases): `‖Ξ‖ ≤ ‖I_emp‖ + ‖M_t‖ + ‖R‖`, `E‖M_t‖² = c_N² Σ E∫‖Kern‖² ≤ 2dTK_ker² q_N`, `q_N ≤ 1`; `N < C`: finitely many `N`,
  pathwise bound `2σ_N K`.
* **P8 `MainRdFieldAux8` + `MainRdFieldTie` (~900): S.A.7**: `hilbert_polar_coupling` on `(M, sb)` gives `(Ω', π, G)` with
  `E‖M_t - G_t‖² ≤ D` and `G` independent of `𝒢 = comap π ℱ_0`, law `νG` (`Measure.ext_of_charFun`, as in `hilbert_martingale_w2`);
  `hilbert_wasserstein_assembly_w1/w2` with `Iemp'` and a measure-level replacement of `I` (the library lemma needs `I`
  `𝒢`-measurable on the same space; `wassersteinE_add_indep_le` is re-proved for laws, ~60 lines); `W₂`: `L²` of `R`, `I`, `M`,
  `G`; `main_rd_field_proof`, `rd_field_wasserstein_one_proof`, `rd_field_wasserstein_two_proof` tied with `type_of%` in `MainRdFieldTie.lean`.

Estimated total ≈ 4.9k lines (P1-P8), under the stop rule 7,000.  S.A.6's last conjunct needs the repair (S1) before the
frozen statement can be tied; everything else is independent of it (the other seven packets are written parametrically).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### P1: Lambda-normalisation -/

/-- The completion constant `C₀'` at the density bound `Λ' ≥ Λ` with `oNΛ d s C₀' Λ' N = oNΛ d s C₀ Λ N`. -/
def sa6_C0norm (d : ℕ) (s C₀ Λ Λ' : ℝ) : ℝ :=
  (C₀ * Λ ^ (s / d) - (if s = 0 then Real.log (Λ' / Λ) / (2 * d) else 0)) / Λ' ^ (s / d)

theorem sa6_oN_normalise {s : ℝ} (hd : 0 < d) {Λ Λ' : ℝ} (hΛ : 0 < Λ) (hΛ' : 0 < Λ') (C₀ : ℝ) {N : ℕ}
    (hN : 0 < N) : oNΛ d s (sa6_C0norm d s C₀ Λ Λ') Λ' N = oNΛ d s C₀ Λ N := by
  unfold oNΛ sa6_C0norm
  have hΛ'p : 0 < Λ' ^ (s / d) := Real.rpow_pos_of_pos hΛ' _
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hs : s = 0
  · subst hs
    simp only [ite_true, zero_div, Real.rpow_zero, div_one, mul_one, zero_sub, Real.rpow_neg_one]
    have l1 : Real.log (N * Λ') = Real.log N + Real.log Λ' := Real.log_mul hNp.ne' hΛ'.ne'
    have l2 : Real.log (N * Λ) = Real.log N + Real.log Λ := Real.log_mul hNp.ne' hΛ.ne'
    have l3 : Real.log (Λ' / Λ) = Real.log Λ' - Real.log Λ := Real.log_div hΛ'.ne' hΛ.ne'
    rw [l1, l2, l3]
    field_simp
    ring
  · simp only [hs, ite_false, zero_add, sub_zero]
    field_simp

theorem sa6_isRegularMF_mono {s : ℝ} {r : ℕ} {Λ Λ' T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (h : IsRegularMFRd s r Λ T ρ) (hΛ : Λ ≤ Λ') : IsRegularMFRd s r Λ' T ρ := by
  unfold IsRegularMFRd at h ⊢
  exact ⟨fun t ht => ⟨(h.1 t ht).1, (h.1 t ht).2.1, (h.1 t ht).2.2.trans hΛ⟩,
    fun hs t ht x => (h.2 hs t ht x).trans hΛ⟩

theorem sa6_pos_of_standing {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 : ℝ}
    {r mV : ℕ} {C₀ : ℝ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) : 0 < Λ := by
  by_contra hneg
  push Not at hneg
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, S.hT.le⟩
  obtain ⟨hcb, hws, hle⟩ := (hS.mean_field.regular 1 le_rfl).1 0 hmem
  have hρ := (hS.mean_field.solution 1 le_rfl).density 0 hmem
  have hws0 : 0 ≤ (weightedSupE r ((d : ℝ) + 3) (S.ρ 1 0)).toReal := ENNReal.toReal_nonneg
  have hall : ∀ x, S.ρ 1 0 x = 0 := by
    intro x
    have h1 := HRS.MP.RdRem.mrr_abs_le_cbNorm hcb x
    have h2 : |S.ρ 1 0 x| ≤ 0 := by linarith
    exact abs_nonpos_iff.1 h2
  have h0 : ∫ x, S.ρ 1 0 x = 0 := by simp [hall]
  have := hρ.integral_one
  linarith

theorem sa6_standing_normalise {S : WholeMainData d} {R : ∀ N, RealizationRd d N}
    {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ} {C₀ : ℝ} {𝔈 : ℕ → ℝ}
    (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {C₀' : ℝ}
    (hC : C₀' = sa6_C0norm d S.s C₀ Λ (max Λ 1))
    (hcomp : CompletionNonnegRd d S.s C₀') :
    RdStanding S R MB (max Λ 1) ΛV G₀ m20 r mV C₀' 𝔈 := by
  have hΛ := sa6_pos_of_standing hS
  have hΛ' : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcorr : ∀ (N : ℕ) (X : EucConfig d N) (t : ℝ), 1 ≤ N →
      correctedEnergyRd S C₀' (max Λ 1) N X t = correctedEnergyRd S C₀ Λ N X t := by
    intro N X t hN
    unfold correctedEnergyRd
    rw [hC, sa6_oN_normalise S.hd hΛ hΛ' C₀ (by omega)]
  refine
    { flow := hS.flow
      mean_field :=
        { solution := hS.mean_field.solution
          datum := hS.mean_field.datum
          regular := fun N hN => sa6_isRegularMF_mono (hS.mean_field.regular N hN) (le_max_left _ _)
          time_derivative := hS.mean_field.time_derivative }
      matrix_bound := hS.matrix_bound
      potential := hS.potential
      energy :=
        { completion := hcomp
          pos := hS.energy.pos
          bound := fun N hN t ht => ?_
          small := hS.energy.small }
      second_moment := hS.second_moment
      filtered := hS.filtered }
  have := hS.energy.bound N hN t ht
  simpa only [hcorr N _ t hN] using this

end HRS.MS.MainRdField
