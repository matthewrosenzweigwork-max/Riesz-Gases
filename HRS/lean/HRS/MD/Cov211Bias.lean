import HRS.MD.Cov211Base
import HRS.Main.EqBiasFinal

/-!
# Packet COV211, the pointwise bias limit `(M_N - M)(θ) / δ_N → B(θ)`

From the proved supercritical bias expansion (`equilibrium_bias_expansion_proof`), tested against
`cos_k` in `L²(μ_θ)` (`V:eq:response-pointwise-bias`), and the interval limit
`δ_N⁻¹ ∫_a^b (C_N - C) → B(b) - B(a)` (`H:eq:covariance-average`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

open HRS

variable {d : ℕ} {s : ℝ}

theorem isSmooth_rateV (k : Lattice d) (β θ : ℝ) : Torus.IsSmooth (rateV k β θ) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k y) := by
    unfold Lattice.dot
    exact ContDiff.sum fun i _ => contDiff_const.mul
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have : Torus.lift (rateV k β θ) =
      fun y => -θ * Real.cos (2 * Real.pi * Lattice.dot k y) / β := by
    funext y
    simp only [Torus.lift, Function.comp, rateV, Torus.cosMode_mk]
  rw [this]
  exact (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))).div_const β

theorem firstMarginal_isProb {N : ℕ} (hN : 0 < N) (P : Measure (Config d N))
    [IsProbabilityMeasure P] : IsProbabilityMeasure (firstMarginal P) := by
  unfold firstMarginal
  rw [dif_pos hN]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 ‹_›

theorem aesm_responseInverse (g : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (ψ : Torus d → ℝ) :
    AEStronglyMeasurable (responseInverse g μ β ψ) μ := by
  unfold responseInverse
  by_cases h : ∃ h, IsResponse g μ β ψ h
  · simp only [h, dite_true]
    exact h.choose_spec.1.aestronglyMeasurable
  · simp only [h, dite_false]
    exact aestronglyMeasurable_const

theorem deltaN_eq (hs1 : (d : ℝ) / 2 < s) (N : ℕ) :
    deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
  unfold deltaN
  rw [if_neg (not_lt.2 hs1.le), if_neg hs1.ne']

theorem deltaN_pos (hs1 : (d : ℝ) / 2 < s) {N : ℕ} (hN : 0 < N) : 0 < deltaN d s N := by
  rw [deltaN_eq hs1]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

/-- `(M_N - M)(θ)/δ_N → B(θ)`. -/
theorem bias_tendsto (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    Tendsto (fun N : ℕ => (rateMeanN d s k β N θ - covM d s β k ρ θ) / deltaN d s N) atTop
      (𝓝 (supercriticalBias d s β (ρ θ) (Torus.cosMode k))) := by
  have hs : (d : ℝ) / 2 ≤ s := hs1.le
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ θ)) := isProb_withDensityReal (hρ θ).1
  set μ := withDensityReal (ρ θ) with hμdef
  obtain ⟨hac, hlim⟩ := Main.equilibrium_bias_expansion_proof hd hs1 hsd (rateV k β θ)
    (isSmooth_rateV k β θ) β hβ (ρ θ) (hρ θ)
  set b := Main.supercriticalBiasDensity d s β (ρ θ) with hb
  have hbm : AEStronglyMeasurable b μ := by
    have : b = fun x => (sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) *
        β ^ ((d : ℝ) / s)) * responseInverse (periodicRiesz d s) μ β (ρ θ) x := by
      funext x; rfl
    rw [this]
    exact (aesm_responseInverse _ _ _ _).const_mul _
  have hB : supercriticalBias d s β (ρ θ) (Torus.cosMode k) =
      ∫ x, b x * Torus.cosMode k x ∂μ := Main.supercriticalBias_eq_integral d s β (ρ θ) _
  set m : ℕ → Measure (Torus d) := fun N => firstMarginal (rateGibbs d s k β θ N) with hm
  set g : ℕ → Torus d → ℝ := fun N y =>
    (((m N).rnDeriv μ y).toReal - 1) / (N : ℝ) ^ (1 - (d : ℝ) / s) - b y with hg
  have hlim' : Tendsto (fun N : ℕ => eLpNorm (g N) 2 μ) atTop (𝓝 0) := hlim
  have hE : Tendsto (fun N : ℕ => (eLpNorm (g N) 2 μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim'
    simpa [Function.comp_def] using this
  have hfin : ∀ᶠ N : ℕ in atTop, eLpNorm (g N) 2 μ < ⊤ :=
    hlim'.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))
  have key : ∀ᶠ N : ℕ in atTop,
      |(rateMeanN d s k β N θ - covM d s β k ρ θ) / deltaN d s N -
        supercriticalBias d s β (ρ θ) (Torus.cosMode k)| ≤ (eLpNorm (g N) 2 μ).toReal := by
    filter_upwards [hfin, eventually_ge_atTop 2] with N hNf hN2
    have hN0 : 0 < N := by omega
    haveI hPN := rateGibbs_isProb hd hs hsd hβ k hN0 θ
    haveI hmN : IsProbabilityMeasure (m N) := firstMarginal_isProb hN0 _
    have hacN : m N ≪ μ := hac N hN2
    set δ := (N : ℝ) ^ (1 - (d : ℝ) / s) with hδ
    have hδpos : 0 < δ := Real.rpow_pos_of_pos (by exact_mod_cast hN0) _
    have hdelta : deltaN d s N = δ := deltaN_eq hs1 N
    set f : Torus d → ℝ := fun y => ((m N).rnDeriv μ y).toReal with hf
    have hfi : Integrable f μ := Measure.integrable_toReal_rnDeriv
    have hcos_m : AEStronglyMeasurable (Torus.cosMode k) μ :=
      (Torus.continuous_cosMode k).aestronglyMeasurable
    have hcos_b : ∀ᵐ x ∂μ, ‖Torus.cosMode k x‖ ≤ 1 :=
      Filter.Eventually.of_forall (Torus.norm_cosMode_le k)
    have hfm : Measurable f := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hgm : AEStronglyMeasurable (g N) μ :=
      (((hfm.sub_const 1).div_const _).aestronglyMeasurable).sub hbm
    have hgL2 : MemLp (g N) 2 μ := hNf
    have hgi : Integrable (g N) μ := hgL2.integrable (by norm_num)
    have hA : Integrable (fun y => (f y - 1) / δ) μ := (hfi.sub (integrable_const _)).div_const _
    have hAc : Integrable (fun y => ((f y - 1) / δ) * Torus.cosMode k y) μ :=
      hA.mul_bdd hcos_m hcos_b
    have hgc : Integrable (fun y => g N y * Torus.cosMode k y) μ := hgi.mul_bdd hcos_m hcos_b
    have hbc : Integrable (fun y => b y * Torus.cosMode k y) μ := by
      have := hAc.sub hgc
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg, Pi.sub_apply]
      ring
    have hMN : rateMeanN d s k β N θ = ∫ y, f y * Torus.cosMode k y ∂μ := by
      unfold rateMeanN
      show ∫ x, Torus.cosMode k x ∂(m N) = _
      exact (integral_toReal_rnDeriv_mul hacN).symm
    have hM : covM d s β k ρ θ = ∫ y, Torus.cosMode k y ∂μ := rfl
    have hfc : Integrable (fun y => f y * Torus.cosMode k y) μ := hfi.mul_bdd hcos_m hcos_b
    have hcc : Integrable (fun y => Torus.cosMode k y) μ :=
      (integrable_const (1 : ℝ)).mono' hcos_m hcos_b
    have hX : (rateMeanN d s k β N θ - covM d s β k ρ θ) / deltaN d s N =
        ∫ y, ((f y - 1) / δ) * Torus.cosMode k y ∂μ := by
      rw [hdelta, hMN, hM, ← integral_sub hfc hcc, ← integral_div]
      congr 1
      funext y
      ring
    have hdiff : (rateMeanN d s k β N θ - covM d s β k ρ θ) / deltaN d s N -
        supercriticalBias d s β (ρ θ) (Torus.cosMode k) = ∫ y, g N y * Torus.cosMode k y ∂μ := by
      rw [hX, hB, ← integral_sub hAc hbc]
      congr 1
      funext y
      simp only [hg]
      ring
    rw [hdiff]
    calc |∫ y, g N y * Torus.cosMode k y ∂μ| ≤ ∫ y, ‖g N y * Torus.cosMode k y‖ ∂μ := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, ‖g N y‖ ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
            hgi.norm (Filter.Eventually.of_forall fun y => ?_)
          show ‖g N y * Torus.cosMode k y‖ ≤ ‖g N y‖
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (Torus.norm_cosMode_le k y)
      _ = (eLpNorm (g N) 1 μ).toReal := by
          rw [integral_norm_eq_lintegral_enorm hgm, eLpNorm_one_eq_lintegral_enorm hgm]
      _ ≤ (eLpNorm (g N) 2 μ).toReal := by
          refine ENNReal.toReal_mono hNf.ne ?_
          exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ =>
    supercriticalBias d s β (ρ θ) (Torus.cosMode k) - (eLpNorm (g N) 2 μ).toReal)
    (h := fun N : ℕ => supercriticalBias d s β (ρ θ) (Torus.cosMode k) + (eLpNorm (g N) 2 μ).toReal)
    ?_ ?_ ?_ ?_
  · simpa using tendsto_const_nhds.sub hE
  · simpa using tendsto_const_nhds.add hE
  · filter_upwards [key] with N hN
    have := (abs_le.1 hN).1
    linarith
  · filter_upwards [key] with N hN
    have := (abs_le.1 hN).2
    linarith

/-- `δ_N⁻¹ ∫_a^b (C_N - C) → B(b) - B(a)` (`H:eq:covariance-average`). -/
theorem avg_tendsto (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (a b : ℝ) :
    Tendsto (fun N : ℕ => (deltaN d s N)⁻¹ * ∫ θ in a..b,
        (rateVarN d s k β N θ - covC d s β k ρ θ)) atTop
      (𝓝 (supercriticalBias d s β (ρ b) (Torus.cosMode k) -
        supercriticalBias d s β (ρ a) (Torus.cosMode k))) := by
  have h := (bias_tendsto hd hs1 hsd β hβ k ρ hρ b).sub (bias_tendsto hd hs1 hsd β hβ k ρ hρ a)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [integral_CN_sub_C hd hs1.le hsd β hβ k hk ρ hρ hN a b]
  ring

end HRS.MD.Cov211
