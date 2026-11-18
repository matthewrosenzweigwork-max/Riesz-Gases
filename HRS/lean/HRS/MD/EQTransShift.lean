import HRS.MD.EQ29Vocab
import HRS.Main.EqBiasFinal
import HRS.Main.EqMargFinal
import HRS.Equilibrium.Q32cAux2

/-!
# EQ-TRANS (b): `eq_shift_limit` (Theorem 2.9, TeX L988-991, proof L3961-3964)

The deterministic shift `centerShift = √N (m_{N,β}(φ) - μ_β(φ))` between the two centerings.

* `s < 2d/3`: `|(m_N - μ)(φ)| ≤ ‖φ‖_∞ ‖dm_N/dμ - 1‖_{L²(μ)} ≤ C δ_N` (`equilibrium_marginal_L2_proof`) and `√N δ_N → 0`.
* `d/2 < s < d`: `(m_N - μ)(φ) = N^{1-d/s}(b(φ) + o(1))` from the proved `equilibrium_bias_expansion_proof`
  paired with the bounded `φ`; `centerShift = N^{3/2-d/s} (b + o(1))`.

Only `supercriticalBias_eq_integral` and the proved bias expansion enter; the sign clause uses nothing more.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQTransShift

open HRS.MD.EQ29 HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

theorem et_deltaN_nonneg {s : ℝ} (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ deltaN d s N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs
  · positivity
  · have : 0 ≤ Real.log (Real.exp 1 * N) := Real.log_nonneg (by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith)
    positivity
  · positivity

theorem et_firstMarginal_isProb {N : ℕ} (hN : 0 < N) (P : Measure (Config d N))
    [IsProbabilityMeasure P] : IsProbabilityMeasure (firstMarginal P) := by
  unfold firstMarginal
  rw [dif_pos hN]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 ‹_›

theorem et_aesm_responseInverse (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (ψ : Torus d → ℝ) :
    AEStronglyMeasurable (responseInverse g μ β ψ) μ := by
  unfold responseInverse
  by_cases h : ∃ h, IsResponse g μ β ψ h
  · simp only [h, dite_true]
    exact h.choose_spec.1.aestronglyMeasurable
  · simp only [h, dite_false]
    exact aestronglyMeasurable_const

/-- The canonical Gibbs law of a thermal density is a probability measure (`N ≥ 1`). -/
theorem et_gibbs_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    PDE.MFDecay.exists_thermal_bounds (by omega : 1 ≤ d) s hs0 hsd β β hβ le_rfl V hVc
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ
  have hρs : SmoothPosDensity ρβ := ⟨hρβ.1, hsm, hpos⟩
  have hΛ : ∀ x, ρβ x ≤ Lam :=
    fun x => (hb β ⟨le_rfl, le_rfl⟩ ρβ hρβ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2
  have hP : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
    obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρβ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1
  rw [hP]
  exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ (Λ := max Lam 1) (le_max_right _ _) hρs.density
    (fun x => (hΛ x).trans (le_max_left _ _)) hN

theorem et_smooth_bound {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous φ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖φ x‖ ≤ M := by
  have hc : Continuous φ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).continuous
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨hc, max M 0, le_max_right _ _, fun x => (hM x (Set.mem_univ x)).trans (le_max_left _ _)⟩

/-- `|∫ g φ dμ| ≤ M ‖g‖_{L²(μ)}` for a probability measure `μ` and `|φ| ≤ M`. -/
theorem et_abs_int_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {g φ : Torus d → ℝ}
    (hg : MemLp g 2 μ) (hφm : AEStronglyMeasurable φ μ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    |∫ y, g y * φ y ∂μ| ≤ M * (eLpNorm g 2 μ).toReal := by
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hgm : AEStronglyMeasurable g μ := hg.aestronglyMeasurable
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (Classical.arbitrary _))
  calc |∫ y, g y * φ y ∂μ| ≤ ∫ y, ‖g y * φ y‖ ∂μ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, M * ‖g y‖ ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hgi.norm.const_mul M) (Filter.Eventually.of_forall fun y => ?_)
        show ‖g y * φ y‖ ≤ M * ‖g y‖
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
    _ = M * (eLpNorm g 1 μ).toReal := by
        rw [integral_const_mul, integral_norm_eq_lintegral_enorm hgm,
          eLpNorm_one_eq_lintegral_enorm hgm]
    _ ≤ M * (eLpNorm g 2 μ).toReal := by
        refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hg.eLpNorm_ne_top ?_) hM0
        exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- `centerShift = √N ∫ (dm_N/dμ - 1) φ dμ` (for `N ≥ 1`, `m_N ≪ μ`). -/
theorem et_centerShift_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {φ : Torus d → ℝ}
    (hφm : AEStronglyMeasurable φ (withDensityReal ρβ)) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M)
    {N : ℕ} (hN : 0 < N)
    (hac : firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ) :
    centerShift d s V β ρβ φ N =
      Real.sqrt N * ∫ y, (((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
        (withDensityReal ρβ) y).toReal - 1) * φ y ∂(withDensityReal ρβ) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  haveI := et_gibbs_prob hd hs0 hsd V hV hβ hρβ hN
  haveI hm : IsProbabilityMeasure (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) :=
    et_firstMarginal_isProb hN _
  set μ := withDensityReal ρβ with hμdef
  set m := firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) with hmdef
  set f : Torus d → ℝ := fun y => (m.rnDeriv μ y).toReal with hf
  have hfi : Integrable f μ := Measure.integrable_toReal_rnDeriv
  have hφb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M := Filter.Eventually.of_forall hM
  have hfc : Integrable (fun y => f y * φ y) μ := hfi.mul_bdd hφm hφb
  have hφi : Integrable φ μ := (integrable_const M).mono' hφm hφb
  unfold centerShift pair
  rw [← integral_toReal_rnDeriv_mul hac]
  congr 1
  rw [← integral_sub hfc hφi]
  congr 1
  funext y
  ring

/-- Elementary: `√N δ_N → 0` for `s < 2d/3`. -/
theorem et_sqrt_mul_deltaN_tendsto {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) :
    Tendsto (fun N : ℕ => Real.sqrt N * deltaN d s N) atTop (𝓝 0) := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < N := by
    filter_upwards [eventually_gt_atTop 0] with N hN using by exact_mod_cast hN
  by_cases h1 : s < (d : ℝ) / 2
  · have hrw : ∀ᶠ N : ℕ in atTop, Real.sqrt N * deltaN d s N = (N : ℝ) ^ (-(1 : ℝ) / 2) := by
      filter_upwards [hpos] with N hN
      unfold deltaN
      have e : (N : ℝ)⁻¹ = (N : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      rw [if_pos h1, Real.sqrt_eq_rpow, e, ← Real.rpow_add hN]
      congr 1; norm_num
    refine Tendsto.congr' (EventuallyEq.symm hrw) ?_
    have h0 : Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num) |>.congr fun x => by congr 1; ring
    exact h0.comp hnat
  by_cases h2 : s = (d : ℝ) / 2
  · have hlog : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp hnat
    have hinv : Tendsto (fun N : ℕ => ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hnat)
    have hsum := hinv.add hlog
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hpos] with N hN
    unfold deltaN
    rw [if_neg h1, if_pos h2, Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp,
      Real.sqrt_eq_rpow]
    have hq : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hN _
    have hsq : (N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hN]; norm_num
    have hinv2 : (N : ℝ)⁻¹ = ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ * ((N : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
      rw [← mul_inv, ← hsq]
    rw [hinv2]
    field_simp
  · have hs1 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hspos : 0 < s := by linarith
    have hexp : (3 : ℝ) / 2 - (d : ℝ) / s < 0 := by
      have : (3 : ℝ) / 2 < (d : ℝ) / s := by
        rw [lt_div_iff₀ hspos]; linarith
      linarith
    have hrw : ∀ᶠ N : ℕ in atTop, Real.sqrt N * deltaN d s N =
        (N : ℝ) ^ (-((d : ℝ) / s - 3 / 2)) := by
      filter_upwards [hpos] with N hN
      unfold deltaN
      rw [if_neg h1, if_neg h2, Real.sqrt_eq_rpow, ← Real.rpow_add hN]
      congr 1; ring
    refine Tendsto.congr' (EventuallyEq.symm hrw) ?_
    exact (tendsto_rpow_neg_atTop (by linarith)).comp hnat

/-- The bias limit `(∫ (dm_N/dμ - 1) φ dμ) / δ_N → b(φ)` for `d/2 < s < d`. -/
theorem et_bias_pair_tendsto (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {φ : Torus d → ℝ}
    (hφm : AEStronglyMeasurable φ (withDensityReal ρβ)) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    Tendsto (fun N : ℕ =>
      (∫ y, (((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
        (withDensityReal ρβ) y).toReal - 1) * φ y ∂(withDensityReal ρβ)) /
          (N : ℝ) ^ (1 - (d : ℝ) / s)) atTop
      (𝓝 (supercriticalBias d s β ρβ φ)) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  set μ := withDensityReal ρβ with hμdef
  obtain ⟨hac, hlim⟩ := Main.equilibrium_bias_expansion_proof hd hs1 hsd V hV β hβ ρβ hρβ
  set b := Main.supercriticalBiasDensity d s β ρβ with hb
  have hbm : AEStronglyMeasurable b μ := by
    have : b = fun x => (sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) *
        β ^ ((d : ℝ) / s)) * responseInverse (periodicRiesz d s) μ β ρβ x := by
      funext x; rfl
    rw [this]
    exact (et_aesm_responseInverse _ _ _ _).const_mul _
  have hB : supercriticalBias d s β ρβ φ = ∫ x, b x * φ x ∂μ :=
    Main.supercriticalBias_eq_integral d s β ρβ φ
  set m : ℕ → Measure (Torus d) := fun N => firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)
    with hm
  set g : ℕ → Torus d → ℝ := fun N y =>
    (((m N).rnDeriv μ y).toReal - 1) / (N : ℝ) ^ (1 - (d : ℝ) / s) - b y with hg
  have hlim' : Tendsto (fun N : ℕ => eLpNorm (g N) 2 μ) atTop (𝓝 0) := hlim
  have hE : Tendsto (fun N : ℕ => (eLpNorm (g N) 2 μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim'
    simpa [Function.comp_def] using this
  have hfin : ∀ᶠ N : ℕ in atTop, eLpNorm (g N) 2 μ < ⊤ :=
    hlim'.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
  have key : ∀ᶠ N : ℕ in atTop,
      |(∫ y, (((m N).rnDeriv μ y).toReal - 1) * φ y ∂μ) / (N : ℝ) ^ (1 - (d : ℝ) / s) -
        supercriticalBias d s β ρβ φ| ≤ M * (eLpNorm (g N) 2 μ).toReal := by
    filter_upwards [hfin, eventually_ge_atTop 2] with N hNf hN2
    have hN0 : 0 < N := by omega
    haveI := et_gibbs_prob hd (by linarith : 0 ≤ s) hsd V hV hβ hρβ hN0
    haveI hmN : IsProbabilityMeasure (m N) := et_firstMarginal_isProb hN0 _
    set δ := (N : ℝ) ^ (1 - (d : ℝ) / s) with hδ
    set f : Torus d → ℝ := fun y => ((m N).rnDeriv μ y).toReal with hf
    have hfi : Integrable f μ := Measure.integrable_toReal_rnDeriv
    have hφb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M := Filter.Eventually.of_forall hM
    have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hgm : AEStronglyMeasurable (g N) μ :=
      (((hfm.sub_const 1).div_const _).aestronglyMeasurable).sub hbm
    have hgL2 : MemLp (g N) 2 μ := hNf
    have hgi : Integrable (g N) μ := hgL2.integrable (by norm_num)
    have hA : Integrable (fun y => (f y - 1) / δ) μ := (hfi.sub (integrable_const _)).div_const _
    have hAc : Integrable (fun y => ((f y - 1) / δ) * φ y) μ := hA.mul_bdd hφm hφb
    have hgc : Integrable (fun y => g N y * φ y) μ := hgi.mul_bdd hφm hφb
    have hbc : Integrable (fun y => b y * φ y) μ := by
      have := hAc.sub hgc
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg, Pi.sub_apply]
      ring
    have hX : (∫ y, (f y - 1) * φ y ∂μ) / δ = ∫ y, ((f y - 1) / δ) * φ y ∂μ := by
      rw [← integral_div]
      congr 1
      funext y
      ring
    have hdiff : (∫ y, (f y - 1) * φ y ∂μ) / δ - supercriticalBias d s β ρβ φ =
        ∫ y, g N y * φ y ∂μ := by
      rw [hX, hB, ← integral_sub hAc hbc]
      congr 1
      funext y
      simp only [hg]
      ring
    rw [hdiff]
    exact et_abs_int_le hgL2 hφm hM
  have hM' : Tendsto (fun N : ℕ => M * (eLpNorm (g N) 2 μ).toReal) atTop (𝓝 0) := by
    simpa using hE.const_mul M
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ =>
    supercriticalBias d s β ρβ φ - M * (eLpNorm (g N) 2 μ).toReal)
    (h := fun N : ℕ => supercriticalBias d s β ρβ φ + M * (eLpNorm (g N) 2 μ).toReal)
    ?_ ?_ ?_ ?_
  · simpa using tendsto_const_nhds.sub hM'
  · simpa using tendsto_const_nhds.add hM'
  · filter_upwards [key] with N hN
    have := (abs_le.1 hN).1
    linarith
  · filter_upwards [key] with N hN
    have := (abs_le.1 hN).2
    linarith

theorem eq_shift_limit_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) :
    (s < 2 * (d : ℝ) / 3 → Tendsto (centerShift d s V β ρβ φ) atTop (𝓝 0)) ∧
    (s = 2 * (d : ℝ) / 3 →
      Tendsto (centerShift d s V β ρβ φ) atTop (𝓝 (supercriticalBias d s β ρβ φ))) ∧
    (2 * (d : ℝ) / 3 < s → supercriticalBias d s β ρβ φ ≠ 0 →
      Tendsto (fun N => |centerShift d s V β ρβ φ N|) atTop atTop) ∧
    (2 * (d : ℝ) / 3 < s → 0 < supercriticalBias d s β ρβ φ →
      Tendsto (centerShift d s V β ρβ φ) atTop atTop) := by
  obtain ⟨hφc, M, hM0, hM⟩ := et_smooth_bound hφ
  have hφm : AEStronglyMeasurable φ (withDensityReal ρβ) := hφc.aestronglyMeasurable
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- the bias part, used when `s ≥ 2d/3`
  have hbias : ∀ hs1 : (d : ℝ) / 2 < s,
      Tendsto (fun N : ℕ => centerShift d s V β ρβ φ N /
        (Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s))) atTop
        (𝓝 (supercriticalBias d s β ρβ φ)) := by
    intro hs1
    refine (et_bias_pair_tendsto hd hs1 hsd V hV hβ hρβ hφm hM).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN0 : 0 < N := by omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    obtain ⟨hac, -⟩ := Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV β β hβ le_rfl |>.choose_spec.2
      β ⟨le_rfl, le_rfl⟩ ρβ hρβ N hN2
    rw [et_centerShift_eq hd hs0 hsd V hV hβ hρβ hφm hM hN0 hac]
    have hδ : 0 < (N : ℝ) ^ (1 - (d : ℝ) / s) := Real.rpow_pos_of_pos hNr _
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    field_simp
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs hb => ?_, fun hs hb => ?_⟩
  · -- `s < 2d/3`
    obtain ⟨C, hC0, hC⟩ := Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV β β hβ le_rfl
    have hlim := (et_sqrt_mul_deltaN_tendsto (d := d) hs0 hs).const_mul (M * C)
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 2] with N hN2
    have hN0 : 0 < N := by omega
    obtain ⟨hac, hL2⟩ := hC β ⟨le_rfl, le_rfl⟩ ρβ hρβ N hN2
    haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
    have hδ0 := et_deltaN_nonneg (d := d) hs0 (show 1 ≤ N by omega)
    have hfm : Measurable (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
        (withDensityReal ρβ) y).toReal - 1) :=
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal).sub_const 1
    have hmem : MemLp (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
        (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ) :=
      lt_of_le_of_lt hL2 ENNReal.ofReal_lt_top
    have hb := et_abs_int_le hmem hφm hM
    have hle : (eLpNorm (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
        (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ)).toReal ≤ C * deltaN d s N :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0.le hδ0) hL2
    rw [Real.norm_eq_abs, et_centerShift_eq hd hs0 hsd V hV hβ hρβ hφm hM hN0 hac, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt N * |∫ y, (((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
          (withDensityReal ρβ) y).toReal - 1) * φ y ∂(withDensityReal ρβ)|
        ≤ Real.sqrt N * (M * (C * deltaN d s N)) := by
          gcongr
          exact hb.trans (mul_le_mul_of_nonneg_left hle hM0)
      _ = M * C * (Real.sqrt N * deltaN d s N) := by ring
  · -- `s = 2d/3`
    have hspos : 0 < s := by linarith
    have hs1 : (d : ℝ) / 2 < s := by linarith
    have hdsr : (d : ℝ) / s = 3 / 2 := by
      rw [div_eq_iff hspos.ne', hs]; ring
    refine (hbias hs1).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have : Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNr, hdsr]
      norm_num
    rw [this, div_one]
  · -- `s > 2d/3`, `b ≠ 0`
    have hspos : 0 < s := by linarith
    have hs1 : (d : ℝ) / 2 < s := by linarith
    have hexp : 0 < Real.sqrt 0 + ((3 : ℝ) / 2 - (d : ℝ) / s) := by
      have : (d : ℝ) / s < 3 / 2 := by
        rw [div_lt_iff₀ hspos]; linarith
      simp; linarith
    have hP : Tendsto (fun N : ℕ => Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s)) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => x ^ ((3 : ℝ) / 2 - (d : ℝ) / s)) atTop atTop :=
        tendsto_rpow_atTop (by simpa using hexp)
      refine (h1.comp hnat).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      try simp only [Function.comp_apply]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNr]
      congr 1; ring
    have habs := (hbias hs1).abs
    have hpos : 0 < |supercriticalBias d s β ρβ φ| := abs_pos.2 hb
    refine (hP.atTop_mul_pos hpos habs).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hδ : 0 < (N : ℝ) ^ (1 - (d : ℝ) / s) := Real.rpow_pos_of_pos hNr _
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    try simp only [Pi.mul_apply]
    rw [abs_div, abs_of_pos (mul_pos hsq hδ)]
    field_simp
  · -- `s > 2d/3`, `b > 0`
    have hspos : 0 < s := by linarith
    have hs1 : (d : ℝ) / 2 < s := by linarith
    have hexp : 0 < (3 : ℝ) / 2 - (d : ℝ) / s := by
      have : (d : ℝ) / s < 3 / 2 := by
        rw [div_lt_iff₀ hspos]; linarith
      linarith
    have hP : Tendsto (fun N : ℕ => Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s)) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => x ^ ((3 : ℝ) / 2 - (d : ℝ) / s)) atTop atTop :=
        tendsto_rpow_atTop hexp
      refine (h1.comp hnat).congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      try simp only [Function.comp_apply]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNr]
      congr 1; ring
    refine (hP.atTop_mul_pos hb (hbias hs1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hδ : 0 < (N : ℝ) ^ (1 - (d : ℝ) / s) := Real.rpow_pos_of_pos hNr _
    have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNr
    try simp only [Pi.mul_apply]
    field_simp

end HRS.MD.EQTransShift

end
