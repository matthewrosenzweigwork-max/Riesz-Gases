import HRS.PDE.MovDAux8

/-!
# MOVD Aux9: uniform integrability from an `L²` bound, and `L¹` convergence (Vitali)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

theorem movd_uniformIntegrable_L2 {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ι → Ω → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ) {B : ℝ}
    (hB : ∀ i, ∫⁻ ω, ‖f i ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) : UniformIntegrable f 1 μ := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top hf fun ε hε => ?_
  by_cases hεt : ε = ⊤
  · exact ⟨1, fun i => by rw [hεt]; exact le_top⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set e : ℝ := ε.toReal with he_def
  set Bp : ℝ := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  set Cr : ℝ := Bp / e + 1 with hCr
  have hCr1 : 1 ≤ Cr := by
    have : 0 ≤ Bp / e := div_nonneg hBp0 he.le
    linarith
  have hCr0 : 0 < Cr := by linarith
  refine ⟨Real.toNNReal Cr, fun i => ?_⟩
  have hC' : ((Real.toNNReal Cr : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cr := rfl
  have hc0 : ENNReal.ofReal Cr ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hCr0
  have hct : ENNReal.ofReal Cr ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB' : ∫⁻ ω, ‖f i ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal Bp :=
    (hB i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hpt : ∀ ω, ‖({x | Real.toNNReal Cr ≤ ‖f i x‖₊}.indicator (f i)) ω‖ₑ ≤
      ‖f i ω‖ₑ ^ 2 * (ENNReal.ofReal Cr)⁻¹ := by
    intro ω
    by_cases hx : Real.toNNReal Cr ≤ ‖f i ω‖₊
    · rw [Set.indicator_of_mem (show ω ∈ {x | Real.toNNReal Cr ≤ ‖f i x‖₊} from hx)]
      have h1 : ENNReal.ofReal Cr ≤ ‖f i ω‖ₑ := by
        rw [← hC']
        exact ENNReal.coe_le_coe.2 hx
      set a : ℝ≥0∞ := ‖f i ω‖ₑ with ha
      calc a = a * 1 := (mul_one a).symm
        _ ≤ a * (a * (ENNReal.ofReal Cr)⁻¹) := by
          gcongr
          calc (1 : ℝ≥0∞) = ENNReal.ofReal Cr * (ENNReal.ofReal Cr)⁻¹ :=
                (ENNReal.mul_inv_cancel hc0 hct).symm
            _ ≤ a * (ENNReal.ofReal Cr)⁻¹ := by gcongr
        _ = a ^ 2 * (ENNReal.ofReal Cr)⁻¹ := by ring
    · rw [Set.indicator_of_notMem (show ω ∉ {x | Real.toNNReal Cr ≤ ‖f i x‖₊} from hx)]
      simp
  have hind : AEStronglyMeasurable ({x | Real.toNNReal Cr ≤ ‖f i x‖₊}.indicator (f i)) μ :=
    (hf i).indicator₀ (nullMeasurableSet_le aemeasurable_const (hf i).nnnorm.aemeasurable)
  rw [eLpNorm_one_eq_lintegral_enorm hind]
  calc ∫⁻ ω, ‖({x | Real.toNNReal Cr ≤ ‖f i x‖₊}.indicator (f i)) ω‖ₑ ∂μ
      ≤ ∫⁻ ω, ‖f i ω‖ₑ ^ 2 * (ENNReal.ofReal Cr)⁻¹ ∂μ := lintegral_mono hpt
    _ = (∫⁻ ω, ‖f i ω‖ₑ ^ 2 ∂μ) * (ENNReal.ofReal Cr)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)
    _ ≤ ENNReal.ofReal Bp * (ENNReal.ofReal Cr)⁻¹ := by gcongr
    _ = ENNReal.ofReal (Bp / Cr) := by
        rw [← ENNReal.ofReal_inv_of_pos hCr0, ← ENNReal.ofReal_mul hBp0, div_eq_mul_inv]
    _ ≤ ε := by
        rw [← ENNReal.ofReal_toReal hεt]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hCr0]
        have : e * Cr = Bp + e := by rw [hCr]; field_simp
        linarith

theorem movd_L1_conv {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : ℕ → Ω → ℝ} {g : Ω → ℝ} (hm : ∀ n, AEStronglyMeasurable (h n) μ) {B : ℝ}
    (hB : ∀ᶠ n in atTop, ∫⁻ ω, ‖h n ω‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 (g ω))) :
    Integrable g μ ∧ Tendsto (fun n => ∫ ω, h n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hB
  have hUI : UniformIntegrable (fun n => h (n + n₀)) 1 μ :=
    movd_uniformIntegrable_L2 (fun n => hm _) (B := B) (fun n => hn₀ _ (by omega))
  have hlim' : ∀ᵐ ω ∂μ, Tendsto (fun n => h (n + n₀) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hlim] with ω hω using hω.comp (tendsto_add_atTop_nat n₀)
  have hgi : Integrable g μ := hUI.integrable_of_ae_tendsto hlim'
  refine ⟨hgi, ?_⟩
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top (fun n => hm _)
    (memLp_one_iff_integrable.2 hgi) hUI.1 hlim'
  have hint : ∀ n, Integrable (h (n + n₀)) μ := fun n =>
    memLp_one_iff_integrable.1 (hUI.memLp n)
  have := tendsto_integral_of_L1' g (Eventually.of_forall hint) hL1
  exact (tendsto_add_atTop_iff_nat n₀).1 this

end HRS

end
