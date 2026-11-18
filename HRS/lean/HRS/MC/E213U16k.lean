import HRS.MC.E213U16j

/-!
# Packet e213u16, file k: past-measurability of the Wick-ordered noise `ℬ^v`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section L2L1

theorem u16_L1_of_L2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {ε : ℝ} (hε : 0 < ε)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ < ENNReal.ofReal (ε ^ 2)) : ∫ ω, |f ω| ∂μ ≤ ε := by
  have hpt : ∀ ω, ‖f ω‖ₑ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (1 / (2 * ε)) * ‖f ω‖ₑ ^ 2 := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : 0 ≤ (ε - |f ω|) ^ 2 := sq_nonneg _
    have : 1 / (2 * ε) * |f ω| ^ 2 = |f ω| ^ 2 / (2 * ε) := by ring
    rw [this, ← sub_nonneg]
    have e : ε / 2 + |f ω| ^ 2 / (2 * ε) - |f ω| = (ε - |f ω|) ^ 2 / (2 * ε) := by
      field_simp
      ring
    rw [e]
    positivity
  have hm : AEMeasurable (fun ω => ‖f ω‖ₑ ^ 2) μ := hf.enorm.pow_const 2
  have hl : ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ENNReal.ofReal ε := by
    calc ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ∫⁻ ω, (ENNReal.ofReal (ε / 2) + ENNReal.ofReal (1 / (2 * ε)) * ‖f ω‖ₑ ^ 2) ∂μ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (1 / (2 * ε)) * ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (1 / (2 * ε)) * ENNReal.ofReal (ε ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring
  have := integral_norm_eq_lintegral_enorm hf
  rw [show (fun ω => |f ω|) = fun ω => ‖f ω‖ from funext fun ω => (Real.norm_eq_abs _).symm, this]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hl

end L2L1


section Wick

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_fc_eq (t : ℝ) (k : NonzeroLattice d) (ω : gd.Ω₀) :
    NegSobolev.fourierCoeff (gd.η t ω) k = NegSobolev.eval (gd.η t ω) (Torus.realMode k) :=
  (HRS.MD.EQGaussWindow.eqgw_eval_realMode _ k).symm

/-- A half-Wick quadratic functional of `η^t`, `t ≤ τ`, which is integrable, is `pastSig τ`-measurable. -/
theorem u16_wick_past {H τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ)
    {μ : Measure (Torus d)} {h : Torus d → Torus d → ℝ} {Q : gd.Ω₀ → ℝ}
    (hW : IsHalfWick gd.P₀ (gd.η t) μ h Q) (hQi : Integrable Q gd.P₀) (hQm : AEStronglyMeasurable Q gd.P₀) :
    AEStronglyMeasurable[pastSig gd τ] Q gd.P₀ := by
  have hm := pastSig_le gd hτ
  refine u16_aesm_of_L1_approx hm hQi fun ε hε => ?_
  have htH : t ∈ Set.Icc (0 : ℝ) H := ⟨ht.1, ht.2.trans hτ.2⟩
  set X : NonzeroLattice d → gd.Ω₀ → ℝ := fun k ω => NegSobolev.fourierCoeff (gd.η t ω) k with hX
  have hXL : ∀ k, MemLp (X k) 2 gd.P₀ := fun k => by
    have := (u16_isSC_pair (gd := gd) htH (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)).memLp_mean.1
    simpa [hX, u16_fc_eq] using this
  set c : NonzeroLattice d → NonzeroLattice d → ℝ :=
    fun k l => ∫ ω', NegSobolev.fourierCoeff (gd.η t ω') k * NegSobolev.fourierCoeff (gd.η t ω') l ∂gd.P₀ with hc
  set QS : Finset (NonzeroLattice d) → gd.Ω₀ → ℝ := fun F ω => (1 / 2) * ∑ k ∈ F, ∑ l ∈ F,
    wickCoeff μ h k l * (X k ω * X l ω - c k l) with hQS
  have hT := hW.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2) by
    exact ENNReal.ofReal_pos.2 (by positivity)))
  obtain ⟨F, hF⟩ := hT.exists
  have hint : Integrable (QS F) gd.P₀ := by
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => ?_
    refine Integrable.const_mul ?_ _
    exact ((hXL k).integrable_mul (hXL l)).sub (integrable_const _)
  refine ⟨QS F, ?_, hint, ?_⟩
  · refine Measurable.aestronglyMeasurable ?_
    letI : MeasurableSpace gd.Ω₀ := pastSig gd τ
    have hXm : ∀ k, Measurable (X k) := fun k => by
      have := pastSig_meas_Xs gd τ (⟨t, ht⟩, ⟨Torus.realMode k, HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k⟩)
      have e : X k = Xs gd τ (⟨t, ht⟩, ⟨Torus.realMode k, HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k⟩) := by
        funext ω
        simp only [hX, Xs, u16_fc_eq]
      rw [e]
      exact this
    exact (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
      (((hXm k).mul (hXm l)).sub_const _).const_mul _).const_mul _
  · have hmeas : AEStronglyMeasurable (fun ω => Q ω - QS F ω) gd.P₀ := hQm.sub hint.aestronglyMeasurable
    exact u16_L1_of_L2 hmeas hε hF

end Wick

end HRS.MC.E213U16

end
