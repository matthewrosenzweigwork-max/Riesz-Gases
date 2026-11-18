import HRS.MC.CepH3E2

/-!
# Packet CEPH3, part E3: finiteness and positivity of the reference measures
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace HRS.MC.CepH3
open HRS HRS.MC.Cepa
noncomputable section
variable {N : ℕ}

/-- The standing analytic hypotheses on the Yosida family, the envelopes and `Ψ`. -/
structure H3 (N : ℕ) (β : ℝ) (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ) (Ψ : Ch N → ℝ) (L : ℝ≥0) : Prop where
  hJ : cep_Yosida 1 N J
  hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z
  hΦle : ∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot 1 N z
  hΦlim : ∀ z, z ∈ cep_Alcove N → Tendsto (fun n : ℕ => Φn n z) atTop (𝓝 (cep_chamberPot 1 N z))
  hΨ : ContDiff ℝ 1 Ψ
  hΨL : LipschitzWith L (gradient Ψ)
  hβ : 0 < β

variable {β : ℝ} {J : ℝ → Ch N → Ch N} {Φn : ℝ → Ch N → ℝ} {Ψ : Ch N → ℝ} {L : ℝ≥0}

lemma H3.Phin_cont (h : H3 N β J Φn Ψ L) {n : ℝ} (hn : 0 < n) : Continuous (Φn n) := by
  refine continuous_iff_continuousAt.mpr fun z => ?_
  exact (h.hΦ n z hn).hasFDerivAt.continuousAt

lemma H3.U_cont (h : H3 N β J Φn Ψ L) {n : ℝ} (hn : 0 < n) : Continuous (fun w => Φn n w + Ψ w) :=
  (h.Phin_cont hn).add h.hΨ.continuous

lemma h3e_gauss_lintegral_lt_top {β : ℝ} (hβ : 0 < β) (K : ℝ) :
    ∫⁻ z : Ch N, ENNReal.ofReal (K * Real.exp (-(1 / (2 * β)) * ‖z‖ ^ 2)) < ⊤ :=
  ((h3e_gauss_integrable (N := N) (b := 1 / (2 * β)) (by positivity)).const_mul K).lintegral_lt_top

lemma h3e_mn_univ [NeZero N] (β : ℝ) (U : Ch N → ℝ) :
    (h3e_mn β U) univ = ∫⁻ z in cep_cell N, cep_cylWeight β U z := by
  unfold h3e_mn
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma h3e_cell_pos [NeZero N] : volume (cep_cell N) ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := h3e_alcove_point (N := N)
  have hopen : IsOpen ((fun z : Ch N => z 0) ⁻¹' Ioo (0:ℝ) 1) := isOpen_Ioo.preimage (by fun_prop)
  have hne : (((fun z : Ch N => z 0) ⁻¹' Ioo (0:ℝ) 1)).Nonempty := ⟨w, by simp [hw0]; norm_num⟩
  refine fun h => (hopen.measure_pos volume hne).ne' (measure_mono_null ?_ h)
  intro z hz
  exact ⟨hz.1.le, hz.2⟩

lemma h3e_E_pos [NeZero N] : volume (cep_cell N ∩ cep_Alcove N) ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := h3e_alcove_point (N := N)
  have hopen : IsOpen (((fun z : Ch N => z 0) ⁻¹' Ioo (0:ℝ) 1) ∩ cep_Alcove N) :=
    (isOpen_Ioo.preimage (by fun_prop)).inter h3b_alcove_isOpen
  have hne : (((fun z : Ch N => z 0) ⁻¹' Ioo (0:ℝ) 1) ∩ cep_Alcove N).Nonempty :=
    ⟨w, by simp [hw0, hw]; norm_num⟩
  refine fun h => (hopen.measure_pos volume hne).ne' (measure_mono_null ?_ h)
  intro z hz
  exact ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩

lemma h3e_lintegral_ne_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : Measurable f) (hpos : ∀ x, f x ≠ 0) (hμ : μ univ ≠ 0) : ∫⁻ x, f x ∂μ ≠ 0 := by
  intro h
  have h1 := (lintegral_eq_zero_iff hf).mp h
  apply hμ
  have h2 : ∀ᵐ x ∂μ, False := by filter_upwards [h1] with x hx; exact hpos x hx
  simpa using ae_iff.mp h2

lemma h3e_weight_ne_zero (β : ℝ) (U : Ch N → ℝ) (z : Ch N) : cep_cylWeight β U z ≠ 0 := by
  unfold cep_cylWeight
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma h3e_mn_ne_zero [NeZero N] {U : Ch N → ℝ} (hU : Measurable U) (β : ℝ) : (h3e_mn β U) univ ≠ 0 := by
  rw [h3e_mn_univ]
  refine h3e_lintegral_ne_zero (h3e_weight_measurable hU) (h3e_weight_ne_zero β U) ?_
  rw [Measure.restrict_apply_univ]; exact h3e_cell_pos

lemma h3e_mn_finite [NeZero N] {U : Ch N → ℝ} {β : ℝ} (hβ : 0 < β) (K : ℝ)
    (hdom : ∀ z ∈ cep_cell N, Real.exp (-(U z) / β) ≤ K * Real.exp (-(1 / (2 * β)) * ‖z‖ ^ 2)) :
    IsFiniteMeasure (h3e_mn β U) := by
  refine ⟨?_⟩
  rw [h3e_mn_univ]
  refine lt_of_le_of_lt ?_ (h3e_gauss_lintegral_lt_top (N := N) hβ K)
  refine (setLIntegral_mono' h3e_cell_measurable fun z hz => ?_).trans (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (hdom z hz)

lemma h3e_mE_le_mn [NeZero N] {U U' : Ch N → ℝ} {β : ℝ} (hβ : 0 < β)
    (hle : ∀ z ∈ cep_Alcove N, U z ≤ U' z) :
    h3e_mE β U' ≤ h3e_mn β U := by
  refine withDensity_mono (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ cep_Alcove N
  · rw [indicator_of_mem hz]
    unfold cep_cylWeight
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    exact div_le_div_of_nonneg_right (neg_le_neg (hle z hz)) hβ.le
  · rw [indicator_of_notMem hz]; exact bot_le

lemma h3e_mE_univ [NeZero N] (β : ℝ) (U : Ch N → ℝ) :
    (h3e_mE β U) univ = ∫⁻ z in cep_Alcove N ∩ cep_cell N, cep_cylWeight β U z := by
  unfold h3e_mE
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_indicator h3b_alcove_isOpen.measurableSet, Measure.restrict_restrict h3b_alcove_isOpen.measurableSet]

lemma h3e_mE_ne_zero [NeZero N] {U : Ch N → ℝ} (hU : Measurable U) (β : ℝ) : (h3e_mE β U) univ ≠ 0 := by
  rw [h3e_mE_univ]
  refine h3e_lintegral_ne_zero (h3e_weight_measurable hU) (h3e_weight_ne_zero β U) ?_
  rw [Measure.restrict_apply_univ, inter_comm]; exact h3e_E_pos
end
end HRS.MC.CepH3
