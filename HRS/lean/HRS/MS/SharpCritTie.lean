import HRS.MS.SharpCritAux2

/-!
# HRS.MS.SharpCritTie -- S7.8 ties

* `sharp_threshold_supercritical_proof : type_of% @HRS.Whole.sharp_threshold_supercritical` (unconditional).
* `sharp_threshold_critical_of_static_field : type_of% @HRS.Whole.quadratic_static_field →
  type_of% @HRS.Whole.sharp_threshold_critical` (the frozen S4.5 is the only missing input; `ScalarCLT`/`CriticalCLT`
  are the intermediate scalar statements, `sharp_threshold_critical_of_clt` the deterministic Slutsky step).
See the scoping report in `HRS/MS/SharpCritAux1.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.Whole.S78

variable {d : ℕ} {s : ℝ}

/-- `A_{d,s} > 0` for `d/2 < s < d`. -/
theorem s78_biasConst_pos (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) : 0 < biasConst d s := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hp1 : 1 < biasP d s := by
    unfold biasP
    rw [lt_div_iff₀ hs0]
    linarith
  have hp2 : biasP d s < 2 := by
    unfold biasP
    rw [div_lt_iff₀ hs0]
    linarith
  unfold biasConst
  have h1 : 0 < sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  have h2 : 0 < Real.Gamma (2 - biasP d s) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < biasP d s := by linarith
  have h4 : 0 < biasP d s - 1 := by linarith
  positivity

/-- `p = d/s < 3/2` for `s > 2d/3`. -/
theorem s78_p_lt (hd : 2 ≤ d) (hs : 2 * (d : ℝ) / 3 < s) : biasP d s < 3 / 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  unfold biasP
  rw [div_lt_iff₀ hs0]
  linarith

/-- Chebyshev for the `L²` norm. -/
theorem s78_cheb {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Z : Ω → ℝ} {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ |Z ω|} ≤ (ENNReal.ofReal t)⁻¹ ^ 2 * eLpNorm Z 2 P ^ 2 := by
  have h := meas_ge_le_mul_pow_eLpNorm_enorm P (p := 2) two_ne_zero ENNReal.ofNat_ne_top
    (f := Z) (ε := ENNReal.ofReal t) (by simpa using ht) (fun h => absurd h ENNReal.ofReal_ne_top)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
  refine le_trans (measure_mono fun ω hω => ?_) h
  simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs] at hω ⊢
  exact ENNReal.ofReal_le_ofReal hω

theorem sharp_threshold_supercritical_proof : type_of% @HRS.Whole.sharp_threshold_supercritical := by
  intro d s hd hs hsd a β ha hβ ρβ hρβ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : (d : ℝ) / 2 < s := by linarith
  have hs0 : 0 < s := by linarith
  obtain rfl := s78_eq_thermalDensity hd hs0 hsd ha hβ hρβ
  obtain ⟨hprob, ⟨M, hM⟩, -, -, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs' hsd a β ha hβ
  have hpos : ∀ x, 0 < thermalDensity d s a β x := s78_thermal_pos hρβ.2
  have hV : 0 < scoreVariance d s β (thermalDensity d s a β) :=
    s78_scoreVariance_pos hd hs' hsd hβ hprob hpos hM
  obtain ⟨C, hC0, hC⟩ := s78_core hd hs' hsd ha hβ
  refine ⟨hV, ⟨C, fun N hN => ?_⟩, ?_⟩
  · have hm : AEStronglyMeasurable (fun X : EucConfig d N => (N : ℝ) ^ (biasP d s - 1) *
          (linStat (thermalDensity d s a β) X -
            pair (withDensityReal (thermalDensity d s a β)) (thermalDensity d s a β)) -
        2 * biasConst d s * β ^ biasP d s * scoreVariance d s β (thermalDensity d s a β))
        (canonicalGibbs (rieszKernel d s) (confinement a) N β) :=
      ((measurable_const.mul ((s78_measurable_linStat hN hprob.measurable).sub_const _)).sub_const _).aestronglyMeasurable
    rw [s78_lhs_eq_eLpNorm _ hm]
    exact hC N hN
  · intro K
    set ρ := thermalDensity d s a β with hρdef
    set p := biasP d s with hp
    set θ := biasTheta d s with hθdef
    have hθ : 0 < θ := s78_biasTheta_pos hd hs' hsd
    have hplt : p < 3 / 2 := s78_p_lt hd hs
    have hA : 0 < biasConst d s := s78_biasConst_pos hd hs' hsd
    set c := 2 * biasConst d s * β ^ p * scoreVariance d s β ρ with hcdef
    have hc : 0 < c := by
      have : 0 < β ^ p := Real.rpow_pos_of_pos hβ _
      positivity
    have hlim1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (p - 3 / 2)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 3 / 2 - p) (by linarith)).comp tendsto_natCast_atTop_atTop
      refine this.congr fun N => ?_
      simp only [Function.comp]
      congr 1
      ring
    have hlim2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop
    have he : Tendsto (fun N : ℕ => ENNReal.ofReal (C * ((N : ℝ) ^ (p - 3 / 2) + (N : ℝ) ^ (-θ))))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (p - 3 / 2) + (N : ℝ) ^ (-θ))) atTop (𝓝 0) := by
        simpa using (hlim1.add hlim2).const_mul C
      simpa using ENNReal.tendsto_ofReal h0
    have hε : (ENNReal.ofReal (c / 2))⁻¹ ^ 2 ≠ ⊤ := by
      refine ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 ?_)
      simpa using hc
    have hG : Tendsto (fun N : ℕ => (ENNReal.ofReal (c / 2))⁻¹ ^ 2 *
        ENNReal.ofReal (C * ((N : ℝ) ^ (p - 3 / 2) + (N : ℝ) ^ (-θ))) ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun N : ℕ => ENNReal.ofReal (C * ((N : ℝ) ^ (p - 3 / 2) + (N : ℝ) ^ (-θ))) ^ 2)
          atTop (𝓝 0) := by
        have h := ((ENNReal.continuous_pow 2).tendsto 0).comp he
        rw [show (0 : ℝ≥0∞) ^ 2 = 0 by simp] at h
        exact h
      simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hε)
    have hev : ∀ᶠ N : ℕ in atTop, K * (N : ℝ) ^ (p - 3 / 2) < c / 2 := by
      have := hlim1.const_mul K
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
      (Eventually.of_forall fun N => bot_le) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    set P := canonicalGibbs (rieszKernel d s) (confinement a) N β with hPdef
    set Z : EucConfig d N → ℝ := fun X => (N : ℝ) ^ (p - 1) *
      (linStat ρ X - pair (withDensityReal ρ) ρ) - c with hZ
    have hsub : {X : EucConfig d N | Real.sqrt N * (linStat ρ X - pair (withDensityReal ρ) ρ) ≤ K} ⊆
        {X | c / 2 ≤ |Z X|} := by
      intro X hX
      simp only [Set.mem_setOf_eq] at hX ⊢
      have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
      have ha : (N : ℝ) ^ (p - 1) = (N : ℝ) ^ (p - 3 / 2) * Real.sqrt N := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]
        congr 1
        ring
      have h1 : (N : ℝ) ^ (p - 1) * (linStat ρ X - pair (withDensityReal ρ) ρ) ≤
          (N : ℝ) ^ (p - 3 / 2) * K := by
        rw [ha, mul_assoc]
        exact mul_le_mul_of_nonneg_left hX (Real.rpow_nonneg hNpos.le _)
      have h2 : Z X ≤ -(c / 2) := by
        simp only [hZ]
        nlinarith
      exact le_trans (by linarith) (neg_le_abs (Z X))
    have hP : IsProbabilityMeasure P := s78_isProb hd hs' hsd ha hβ hN1
    calc P {X | Real.sqrt N * (linStat ρ X - pair (withDensityReal ρ) ρ) ≤ K}
        ≤ P {X | c / 2 ≤ |Z X|} := measure_mono hsub
      _ ≤ (ENNReal.ofReal (c / 2))⁻¹ ^ 2 * eLpNorm Z 2 P ^ 2 := s78_cheb P (by linarith)
      _ ≤ _ := by
        gcongr
        exact hC N hN1

/-! ### The critical case, conditional on the scalar CLT (the scalar content of S4.5) -/

/-- `E_{P_{N,β}} μ_N(ρ_β) = ∫ ρ_β dm_N`, `m_N` the first marginal. -/
theorem s78_E_eq (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, linStat (thermalDensity d s a β) X ∂(canonicalGibbs (rieszKernel d s) (confinement a) N β) =
      pair (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β)) (thermalDensity d s a β) := by
  obtain ⟨hprob, ⟨M, hM⟩, -, hcan, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  have := s78_isProb hd hs hsd ha hβ hN
  have hexch : IsExchangeable (canonicalGibbs (rieszKernel d s) (confinement a) N β) := by
    rw [hcan N]
    exact modulatedGibbs_isExchangeable (rieszKernel d s) β _ (fun x => rieszKernel_neg x)
  exact s78_integral_linStat hN hexch hprob.measurable
    (fun x => by rw [abs_of_nonneg (hprob.nonneg x)]; exact hM x)

/-- The scalar exactly-centred central limit theorem at the critical exponent, for the single test
`ρ_β`: `√N(μ_N(ρ_β) - m_N(ρ_β)) ⇒ N(0, V_ρ)` under `P_{N,β}` (`m_N = E μ_N` the first marginal).  This is the
scalar content of S4.5 `quadratic_static_field` (feature family `φ_0 = ρ_β`, `φ_j = 0`), which is not proved. -/
def ScalarCLT (d : ℕ) (s a β : ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ X, f (Real.sqrt N * (linStat (thermalDensity d s a β) X -
      pair (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) N β)) (thermalDensity d s a β)))
    ∂(canonicalGibbs (rieszKernel d s) (confinement a) N β)) atTop
    (𝓝 (∫ y, f y ∂(gaussianReal 0 (Real.toNNReal (scoreVariance d s β (thermalDensity d s a β))))))

/-- The scalar CLT for every critical parameter. -/
def CriticalCLT : Prop :=
  ∀ (d : ℕ) (s : ℝ), 2 ≤ d → s = 2 * (d : ℝ) / 3 → ∀ a β : ℝ, 0 < a → 0 < β → ScalarCLT d s a β

theorem sharp_threshold_critical_of_clt (hclt : CriticalCLT) :
    type_of% @HRS.Whole.sharp_threshold_critical := by
  intro d s hd hs a β ha hβ ρβ hρβ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : (d : ℝ) / 2 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  have hp : biasP d s = 3 / 2 := by
    unfold biasP
    rw [hs]
    field_simp
  have hclt' := hclt d s hd hs a β ha hβ
  obtain rfl := s78_eq_thermalDensity hd hs0 hsd ha hβ hρβ
  obtain ⟨hprob, ⟨M, hM⟩, -, -, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs' hsd a β ha hβ
  have hpos : ∀ x, 0 < thermalDensity d s a β x := s78_thermal_pos hρβ.2
  have hV : 0 < scoreVariance d s β (thermalDensity d s a β) :=
    s78_scoreVariance_pos hd hs' hsd hβ hprob hpos hM
  refine ⟨hV, fun N hN => s78_isProb hd hs' hsd ha hβ hN, ?_⟩
  intro f
  set ρ := thermalDensity d s a β with hρdef
  set ν : Measure ℝ := gaussianReal 0 (Real.toNNReal (scoreVariance d s β ρ)) with hν
  set c0 : ℝ := 2 * biasConst d s * β ^ ((3 : ℝ) / 2) * scoreVariance d s β ρ with hc0
  obtain ⟨Kb, hKb0, hKb⟩ := s78_bias_est hd hs' hsd ha hβ
  have hθ : 0 < biasTheta d s := s78_biasTheta_pos hd hs' hsd
  have hP : ∀ n : ℕ, IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) (n + 1) β) :=
    fun n => s78_isProb hd hs' hsd ha hβ (by omega)
  set T : ∀ n : ℕ, EucConfig d (n + 1) → ℝ := fun n X => Real.sqrt ((n + 1 : ℕ) : ℝ) *
    (linStat ρ X - pair (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) (n + 1) β)) ρ) with hT
  have hTm : ∀ n : ℕ, Measurable (T n) := fun n =>
    measurable_const.mul ((s78_measurable_linStat (by omega) hprob.measurable).sub_const _)
  have hcl : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun n : ℕ => ∫ X, g (T n X)
      ∂(canonicalGibbs (rieszKernel d s) (confinement a) (n + 1) β)) atTop (𝓝 (∫ y, g y ∂ν)) :=
    fun g => (tendsto_add_atTop_iff_nat 1).2 (hclt' g)
  set b : ℕ → ℝ := fun n => Real.sqrt ((n + 1 : ℕ) : ℝ) *
    (pair (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) (n + 1) β)) ρ -
      pair (withDensityReal ρ) ρ) with hbdef
  have hb : Tendsto b atTop (𝓝 c0) := by
    have hlim2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (by have := hlim2.const_mul Kb; rwa [mul_zero] at this)
    have h1 := hKb (n + 1) (by omega)
    rw [s78_E_eq hd hs' hsd ha hβ (by omega : 1 ≤ n + 1), hp] at h1
    rw [Real.dist_eq]
    have e1 : ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2 - 1) = Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [e1] at h1
    exact h1
  have hsh := s78_shift (fun n : ℕ => canonicalGibbs (rieszKernel d s) (confinement a) (n + 1) β) T hTm ν
    hcl b c0 hb f
  have hlim : ∫ y, f (y + c0) ∂ν = ∫ y, f y ∂(gaussianReal c0 (Real.toNNReal (scoreVariance d s β ρ))) := by
    have hm := integral_map (μ := ν) (φ := fun y : ℝ => y + c0) (measurable_id.add_const c0).aemeasurable
      (f := f) f.continuous.aestronglyMeasurable
    rw [← hm, hν, gaussianReal_map_add_const, zero_add]
  rw [hlim] at hsh
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  refine hsh.congr fun n => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [hT, hbdef]
  congr 1
  ring

/-! ### Derivation of the scalar CLT from S4.5 -/

/-- The feature family `φ_0 = ρ`, `φ_j = 0` (`j ≥ 1`). -/
def s78_phi (ρ : Euc d → ℝ) : ℕ → Euc d → ℝ := fun j => if j = 0 then ρ else fun _ => 0

theorem s78_memCb_zero (J : ℕ) : MemCb J (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun j _ => ⟨0, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  simp [iteratedFDeriv_fun_zero]

theorem s78_cbNorm_zero (J : ℕ) : cbNorm J (fun _ : Euc d => (0 : ℝ)) = 0 := by
  unfold cbNorm
  simp [iteratedFDeriv_fun_zero]

theorem s78_phi_summable (J : ℕ) {ρ : Euc d → ℝ} (hρ : MemCb J ρ) :
    IsSummableFeatureFamily J (s78_phi ρ) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold s78_phi
    split_ifs
    · exact hρ
    · exact s78_memCb_zero J
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    have : j ≠ 0 := by simpa using hj
    simp only [s78_phi, if_neg this]
    exact s78_cbNorm_zero J


theorem s78_memCb_thermal (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (J : ℕ) : MemCb J (thermalDensity d s a β) := by
  obtain ⟨hcd, -, -, -, h5, -⟩ := HRS.MS.Thm.euc_thermal_regularity_proof hd hs0 hsd a β ha hβ
  refine ⟨hcd.of_le (by exact_mod_cast le_top), fun j _ => ?_⟩
  obtain ⟨-, K, hK⟩ := h5 j
  exact ⟨K, by rintro _ ⟨x, rfl⟩; exact hK x⟩

/-- `R P_μ 0 = 0` a.e. -/
theorem s78_responseInverse_zero (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    responseInverse (rieszKernel d s) (withDensityReal ρ) β (fun _ => (0 : ℝ)) =ᵐ[withDensityReal ρ] 0 := by
  have := HRS.MS.Wr.wr13a_isProb_density hρ
  obtain ⟨-, -, -, hmain⟩ := convolution_susceptibility hd hs hsd ρ hρ M hM β hβ
  have h0 : MemL2Zero (withDensityReal ρ) (fun _ => (0 : ℝ)) := ⟨memLp_const (0 : ℝ), by simp⟩
  obtain ⟨hex, huniq, -⟩ := hmain _ h0
  have hz : IsResponse (rieszKernel d s) (withDensityReal ρ) β (fun _ => (0 : ℝ)) (fun _ => 0) := by
    refine ⟨h0, ae_of_all _ fun x => ?_⟩
    simp [Kop, projMean, pair]
  have hspec : IsResponse (rieszKernel d s) (withDensityReal ρ) β (fun _ => (0 : ℝ))
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β (fun _ => (0 : ℝ))) := by
    unfold responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  exact huniq _ _ hspec hz


theorem s78_cov (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (i j : ℕ) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β
      (s78_phi (thermalDensity d s a β) i) (s78_phi (thermalDensity d s a β) j) =
      if i = 0 ∧ j = 0 then scoreVariance d s β (thermalDensity d s a β) else 0 := by
  obtain ⟨hprob, ⟨M, hM⟩, -, -, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi; subst hj
      simp only [s78_phi, if_true, and_self]
      rfl
    · have hz := s78_responseInverse_zero hd hs hsd hβ hprob hM
      simp only [s78_phi, hi, hj, if_true, if_false, and_false]
      unfold susceptibilityCov l2Inner
      have hz' : responseInverse (rieszKernel d s) (thermalMeasure d s a β) β (fun _ => (0 : ℝ)) =ᵐ[thermalMeasure d s a β] 0 := hz
      refine (integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
      exact hz'.mono fun x hx => by
        show _ * _ = (0 : ℝ)
        rw [show responseInverse (rieszKernel d s) (thermalMeasure d s a β) β (fun _ => (0 : ℝ)) x = 0 from hx]
        simp
  · simp only [s78_phi, hi, if_false, false_and]
    simp [susceptibilityCov, l2Inner, projMean, pair]

theorem s78_ext_seq (z w : SeqL2) (h : ∀ i, SeqL2.coord z i = SeqL2.coord w i) : z = w :=
  lp.ext (funext h)

theorem s78_ofSeq_lp (f : lp (fun _ : ℕ => ℝ) 2) :
    SeqL2.ofSeq (fun j => (f : ∀ j : ℕ, ℝ) j) = (f : SeqL2) := by
  have h : Memℓp (fun j => (f : ∀ j : ℕ, ℝ) j) 2 := lp.memℓp f
  exact (dif_pos h).trans rfl

theorem s78_E_eq_single (x : ℝ) : s78_E x = ((lp.single 2 0 x : lp (fun _ : ℕ => ℝ) 2) : SeqL2) := by
  apply s78_ext_seq
  intro i
  rw [s78_coord_E]
  show _ = ((lp.single 2 0 x : lp (fun _ : ℕ => ℝ) 2) : ∀ j : ℕ, ℝ) i
  rw [lp.single_apply]
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

theorem s78_featureVec_eq {N : ℕ} (ρ : Euc d → ℝ) (ν : Measure (Euc d)) (X : EucConfig d N) :
    featureVec (s78_phi ρ) ν X = s78_E (Real.sqrt N * (linStat ρ X - pair ν ρ)) := by
  set T : ℝ := Real.sqrt N * (linStat ρ X - pair ν ρ) with hT
  have hc : (fun j => Real.sqrt N * (pair (empirical X) (s78_phi ρ j) - pair ν (s78_phi ρ j))) =
      fun j => (lp.single 2 0 T : lp (fun _ : ℕ => ℝ) 2) j := by
    funext j
    rw [lp.single_apply]
    by_cases hj : j = 0
    · subst hj
      simp [s78_phi, hT, linStat]
    · simp [s78_phi, hj, pair]
  rw [s78_E_eq_single]
  unfold featureVec
  rw [hc]
  exact s78_ofSeq_lp _


/-- **The scalar CLT follows from S4.5.**  If the frozen `quadratic_static_field` (S4.5) holds, then `ScalarCLT`
holds (feature family `φ_0 = ρ_β`, `φ_j = 0`: the `C_b²(ℓ²)` bound gives convergence of the trigonometric
moments of `√N(μ_N(ρ_β)-m_N(ρ_β))` to those of `N(0,V_ρ)`, and Lévy's theorem finishes). -/
theorem s78_criticalCLT_of_static_field (hsf : type_of% @HRS.Whole.quadratic_static_field) :
    CriticalCLT := by
  intro d s hd hs a β ha hβ f
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : (d : ℝ) / 2 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  have hp : biasP d s = 3 / 2 := by
    unfold biasP
    rw [hs]
    field_simp
  obtain ⟨hprob, ⟨M, hM⟩, -, -, -⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs' hsd a β ha hβ
  have hth := HRS.Whole.S71.s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  have hpos : ∀ x, 0 < thermalDensity d s a β x := s78_thermal_pos hth.2
  have hV : 0 < scoreVariance d s β (thermalDensity d s a β) :=
    s78_scoreVariance_pos hd hs' hsd hβ hprob hpos hM
  set v : ℝ≥0 := Real.toNNReal (scoreVariance d s β (thermalDensity d s a β)) with hvdef
  have hvV : (v : ℝ) = scoreVariance d s β (thermalDensity d s a β) := Real.coe_toNNReal _ hV.le
  set J : ℕ := d + 3 with hJdef
  have hJ : (d : ℝ) / 2 + 2 < J := by rw [hJdef]; push_cast; linarith
  obtain ⟨C, hC⟩ := hsf hd hs0.le hsd a β ha hβ J hJ
  have hφ := s78_phi_summable J (s78_memCb_thermal hd hs0 hsd ha hβ J)
  set S := featureSum J (s78_phi (thermalDensity d s a β)) with hS
  have hγ : IsCenteredGaussianSeq (s78_gamma v)
      (fun i j => susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β (s78_phi (thermalDensity d s a β) i) (s78_phi (thermalDensity d s a β) j)) := by
    refine ⟨s78_gamma_centered v, fun i j => ⟨(s78_gamma_cov v i j).1, ?_⟩⟩
    beta_reduce
    rw [(s78_gamma_cov v i j).2, s78_cov hd hs' hsd ha hβ i j]
    split_ifs <;> simp [hvV]
  set ε : ℕ → ℝ := fun n => C * (S + S ^ 2) * Real.sqrt (deltaN d s (n + 2)) with hεdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hp1 : 0 < biasP d s - 1 := by rw [hp]; norm_num
    have h1 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(biasP d s - 1))) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 2).2 ((tendsto_rpow_neg_atTop hp1).comp tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => deltaN d s (n + 2)) atTop (𝓝 0) := by
      refine h1.congr fun n => ?_
      rw [s78_deltaN_eq hs']
      congr 1
      ring
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    simpa using h3.const_mul (C * (S + S ^ 2))
  have hP : ∀ n : ℕ, IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β) :=
    fun n => s78_isProb hd hs' hsd ha hβ (by omega)
  set T : ∀ n : ℕ, EucConfig d (n + 2) → ℝ := fun n X => Real.sqrt ((n + 2 : ℕ) : ℝ) *
    (linStat (thermalDensity d s a β) X - pair (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β)) (thermalDensity d s a β)) with hT
  have hTm : ∀ n : ℕ, Measurable (T n) := fun n =>
    measurable_const.mul ((s78_measurable_linStat (by omega) hprob.measurable).sub_const _)
  have hsm : ∀ n : ℕ, smoothDist 2
      ((canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β).map fun X => s78_E (T n X))
      (s78_gamma v) ≤ ε n := by
    intro n
    have hc := (hC (s78_phi (thermalDensity d s a β)) hφ (n + 2) (by omega) (s78_gamma v) hγ).2.2.1
    have e : featureVec (s78_phi (thermalDensity d s a β))
        (firstMarginal (canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β)) =
        fun X => s78_E (T n X) := funext fun X => s78_featureVec_eq _ _ X
    simp only [law] at hc
    rw [e] at hc
    exact hc
  have key := s78_weak_of_trig (fun n : ℕ => canonicalGibbs (rieszKernel d s) (confinement a) (n + 2) β) T hTm
    (gaussianReal 0 v) ε hε
    (fun t n => s78_trig_dist _ (hTm n) v Real.contDiff_cos s78_cos_bound (hsm n) t)
    (fun t n => s78_trig_dist _ (hTm n) v Real.contDiff_sin s78_sin_bound (hsm n) t) f
  exact (tendsto_add_atTop_iff_nat 2).1 key

/-- **S7.8, critical case, conditional on S4.5**: the frozen `sharp_threshold_critical` follows from the frozen
`quadratic_static_field` (S4.5), which is the only missing input. -/
theorem sharp_threshold_critical_of_static_field (hsf : type_of% @HRS.Whole.quadratic_static_field) :
    type_of% @HRS.Whole.sharp_threshold_critical :=
  sharp_threshold_critical_of_clt (s78_criticalCLT_of_static_field hsf)

end HRS.Whole.S78
