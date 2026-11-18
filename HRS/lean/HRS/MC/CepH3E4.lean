import HRS.MC.CepH3E3

/-!
# Packet CEPH3, part E4: narrow convergence of the pushed-forward regularised reference measures
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ} {β : ℝ} {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0}

lemma h3e_toReal_weight (β : ℝ) (U : Ch N → ℝ) (z : Ch N) :
    (cep_cylWeight β U z).toReal = Real.exp (-(U z) / β) := by
  unfold cep_cylWeight
  exact ENNReal.toReal_ofReal (Real.exp_nonneg _)

lemma h3e_weight_tendsto_mem [NeZero N] (h : H3 N β J Φn Ψ L) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    Tendsto (fun n : ℕ => (cep_cylWeight β (fun w => Φn n w + Ψ w) z).toReal) atTop
      (𝓝 (Real.exp (-(cep_chamberPot 1 N z + Ψ z) / β))) := by
  simp_rw [h3e_toReal_weight]
  exact (Real.continuous_exp.tendsto _).comp (((h.hΦlim z hz).add_const (Ψ z)).neg.div_const β)

lemma h3e_weight_tendsto_out [NeZero N] (h : H3 N β J Φn Ψ L) {z : Ch N} (hz : z ∉ closure (cep_Alcove N)) :
    Tendsto (fun n : ℕ => (cep_cylWeight β (fun w => Φn n w + Ψ w) z).toReal) atTop (𝓝 0) := by
  obtain ⟨w, hw, -⟩ := h3e_alcove_point (N := N)
  have hc := h3b_c_tendsto h.hJ h.hΦlim hw
  obtain ⟨n₁, hn₁⟩ := (hc.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))).exists_forall_of_atTop
  have hd : 0 < Metric.infDist z (cep_Alcove N) := by
    have := (isClosed_closure (s := cep_Alcove N)).notMem_iff_infDist_pos ⟨w, subset_closure hw⟩ |>.mp hz
    rwa [Metric.infDist_closure] at this
  set d := Metric.infDist z (cep_Alcove N) with hdd
  set B' : ℝ := (N : ℝ) * Real.log 2 + 1 - Ψ z with hB'
  have hlim : Tendsto (fun n : ℕ => Real.exp (B' / β - (n : ℝ) * (d ^ 2 / (2 * β)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (d ^ 2 / (2 * β))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by have := h.hβ; positivity)
    have h2 : Tendsto (fun n : ℕ => B' / β + -((n : ℝ) * (d ^ 2 / (2 * β)))) atTop atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp h1)
    have := Real.tendsto_exp_atBot.comp h2
    exact this.congr (fun n => by simp [sub_eq_add_neg])
  refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop (max n₁ 1)] with n hn
  have hn1 : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by
    have : 1 ≤ n := (le_max_right _ _).trans hn
    exact_mod_cast this
  rw [h3e_toReal_weight]
  refine Real.exp_le_exp.mpr ?_
  have hlow := h3b_Phin_lower h.hJ h.hΦ hnpos w z
  have hcn := hn₁ n hn1
  have : -(Φn n z + Ψ z) ≤ B' - n * (d ^ 2 / 2) := by
    rw [hB']; linarith
  calc -(Φn n z + Ψ z) / β ≤ (B' - n * (d ^ 2 / 2)) / β := div_le_div_of_nonneg_right this h.hβ.le
    _ = B' / β - n * (d ^ 2 / (2 * β)) := by field_simp

lemma h3e_chamberPot_measurable : Measurable (cep_chamberPot 1 (N := N)) := by
  unfold cep_chamberPot
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_) _
  by_cases hkl : k < l
  · simp only [hkl, if_true]
    exact (Real.measurable_log.comp ((by fun_prop : Measurable fun z : Ch N => 2 * Real.sin (Real.pi * (z l - z k))))).neg
  · simp [hkl]

lemma h3e_integral_map_mn [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (β : ℝ) {U : Ch N → ℝ} (hU : Measurable U)
    {φ : Config 1 N → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂((h3e_mn β U).map (h3d_Q σ₀)) =
      ∫ z in cep_cell N, (cep_cylWeight β U z).toReal * φ (h3d_Q σ₀ z) := by
  rw [integral_map (h3d_Q_measurable σ₀).aemeasurable hφ.aestronglyMeasurable]
  unfold h3e_mn
  rw [integral_withDensity_eq_integral_toReal_smul (h3e_weight_measurable hU)
    (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  rfl

lemma h3e_integral_map_mE [NeZero N] (σ₀ : Equiv.Perm (Fin N)) (β : ℝ) {U : Ch N → ℝ} (hU : Measurable U)
    {φ : Config 1 N → ℝ} (hφ : Continuous φ) :
    ∫ x, φ x ∂((h3e_mE β U).map (h3d_Q σ₀)) =
      ∫ z in cep_cell N, (((cep_Alcove N).indicator (cep_cylWeight β U)) z).toReal * φ (h3d_Q σ₀ z) := by
  rw [integral_map (h3d_Q_measurable σ₀).aemeasurable hφ.aestronglyMeasurable]
  unfold h3e_mE
  rw [integral_withDensity_eq_integral_toReal_smul
    ((h3e_weight_measurable hU).indicator h3b_alcove_isOpen.measurableSet)
    (Eventually.of_forall fun z => by
      by_cases hz : z ∈ cep_Alcove N
      · rw [indicator_of_mem hz]; exact ENNReal.ofReal_lt_top
      · rw [indicator_of_notMem hz]; exact ENNReal.zero_lt_top)]
  rfl

/-- Narrow convergence of the pushed-forward regularised reference measures. -/
theorem h3e_conv [NeZero N] (h : H3 N β J Φn Ψ L) (σ₀ : Equiv.Perm (Fin N)) {φ : Config 1 N → ℝ}
    (hφ : Continuous φ) :
    Tendsto (fun n : ℕ => ∫ x, φ x ∂((h3e_mn β (fun w => Φn n w + Ψ w)).map (h3d_Q σ₀))) atTop
      (𝓝 (∫ x, φ x ∂((h3e_mE β (fun w => cep_chamberPot 1 N w + Ψ w)).map (h3d_Q σ₀)))) := by
  obtain ⟨n₀, K, hn₀, hK, hdom⟩ := h3e_dominated h.hJ h.hΦ h.hΦlim h.hΨ h.hΨL h.hβ
  obtain ⟨Cφ, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hQc := h3d_Q_continuous σ₀
  have hUc : ∀ n : ℕ, 1 ≤ n → Continuous (fun w => Φn n w + Ψ w) := fun n hn =>
    h.U_cont (by exact_mod_cast hn)
  have hUlim : Measurable (fun w => cep_chamberPot 1 N w + Ψ w) :=
    (h3e_chamberPot_measurable).add h.hΨ.continuous.measurable
  have key : Tendsto (fun n : ℕ => ∫ z in cep_cell N,
      (cep_cylWeight β (fun w => Φn n w + Ψ w) z).toReal * φ (h3d_Q σ₀ z)) atTop
      (𝓝 (∫ z in cep_cell N,
        (((cep_Alcove N).indicator (cep_cylWeight β (fun w => cep_chamberPot 1 N w + Ψ w))) z).toReal *
          φ (h3d_Q σ₀ z))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z => K * Cφ * Real.exp (-(1 / (2 * β)) * ‖z‖ ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop n₀] with n hn
      exact (((h3e_weight_measurable (hUc n (hn₀.trans hn)).measurable).ennreal_toReal).mul
        (hφ.comp hQc).measurable).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop n₀] with n hn
      refine (ae_restrict_iff' h3e_cell_measurable).mpr (Eventually.of_forall fun z hz => ?_)
      rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, h3e_toReal_weight]
      exact mul_le_mul ((hdom n hn z hz).trans (le_of_eq rfl)) (hC _ (mem_univ _)) (norm_nonneg _)
        (mul_nonneg hK.le (Real.exp_nonneg _)) |>.trans (le_of_eq (by ring))
    · exact ((h3e_gauss_integrable (N := N) (b := 1 / (2 * β)) (by have := h.hβ; positivity)).const_mul
        (K * Cφ)).restrict
    · have hnull := measure_eq_zero_iff_ae_notMem.mp (h3e_boundary_null (N := N))
      refine ae_restrict_of_ae ?_
      filter_upwards [hnull] with z hz
      by_cases hzA : z ∈ cep_Alcove N
      · rw [indicator_of_mem hzA, h3e_toReal_weight]
        exact (h3e_weight_tendsto_mem h hzA).mul_const _
      · have hzc : z ∉ closure (cep_Alcove N) := fun hc => hz ⟨hc, hzA⟩
        rw [indicator_of_notMem hzA, ENNReal.toReal_zero, zero_mul]
        simpa using (h3e_weight_tendsto_out h hzc).mul_const (φ (h3d_Q σ₀ z))
  rw [h3e_integral_map_mE σ₀ β hUlim hφ]
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop n₀] with n hn
  rw [h3e_integral_map_mn σ₀ β (hUc n (hn₀.trans hn)).measurable hφ]
end
end HRS.MC.CepH3
