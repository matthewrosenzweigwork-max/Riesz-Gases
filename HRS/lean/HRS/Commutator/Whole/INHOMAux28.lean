import HRS.Commutator.Whole.INHOMAux27

/-!
# CMX-INHOM auxiliary 28: Minkowski for the Sobolev seminorm, `H^{-α} ≤ L²`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma inhom_sobSqE_rpow (t : ℝ) (F : Euc d → ℂ) :
    sobSqE t F = ∫⁻ ξ, (ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (t / 2)) * ‖F ξ‖ₑ) ^ (2 : ℝ) := by
  unfold sobSqE
  refine lintegral_congr fun ξ => ?_
  have hwpos : 0 < 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := inhom_wt_pos ξ
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ENNReal.rpow_two, ENNReal.rpow_two]
  congr 1
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hwpos.le _),
    ← Real.rpow_natCast ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (t / 2)) 2, ← Real.rpow_mul hwpos.le]
  congr 2
  push_cast; ring

/-- Minkowski: `‖u + δ‖_{H^t} ≤ ‖u‖_{H^t} + ‖δ‖_{H^t}`. -/
lemma inhom_sob_minkowski {u δ w : Euc d → ℝ} (hu : MemLp u 2 volume) (hδ : MemLp δ 2 volume)
    (hw : ∀ x, w x = u x + δ x) (t : ℝ) :
    sobSqE t (HRS.PDE.ToolboxRd.fourierL2 w) ^ ((1 : ℝ) / 2) ≤
      sobSqE t (HRS.PDE.ToolboxRd.fourierL2 u) ^ ((1 : ℝ) / 2) +
        sobSqE t (HRS.PDE.ToolboxRd.fourierL2 δ) ^ ((1 : ℝ) / 2) := by
  have hwe : w = fun x => u x + δ x := funext hw
  have hadd : HRS.PDE.ToolboxRd.fourierL2 w =ᵐ[volume] fun ξ =>
      HRS.PDE.ToolboxRd.fourierL2 u ξ + HRS.PDE.ToolboxRd.fourierL2 δ ξ := by
    rw [hwe]
    exact HRS.PDE.ToolboxRd.FourierAux.fourierL2_add hu hδ
  set wt : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (t / 2)) with hwt
  have hwtm : Measurable wt := by
    refine Measurable.ennreal_ofReal (Measurable.pow_const ?_ _)
    fun_prop
  have hum := (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hu).enorm
  have hδm := (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hδ).enorm
  have hmink := ENNReal.lintegral_Lp_add_le (μ := (volume : Measure (Euc d))) (p := 2)
    (f := fun ξ => wt ξ * ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ₑ)
    (g := fun ξ => wt ξ * ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ)
    (hwtm.aemeasurable.mul hum) (hwtm.aemeasurable.mul hδm) (by norm_num)
  simp only [inhom_sobSqE_rpow]
  calc _ ≤ (∫⁻ ξ, ((fun ξ => wt ξ * ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ₑ) +
        fun ξ => wt ξ * ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ) ξ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
        filter_upwards [hadd] with ξ hξ
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        simp only [Pi.add_apply]
        rw [hξ, ← mul_add]
        gcongr
        exact enorm_add_le _ _
    _ ≤ _ := by simpa using hmink

/-- `‖δ‖_{H^t} ≤ ‖δ‖_{L²}` for `t ≤ 0`. -/
lemma inhom_sob_le_L2 {δ : Euc d → ℝ} (hδ : MemLp δ 2 volume) {t : ℝ} (ht : t ≤ 0) :
    sobSqE t (HRS.PDE.ToolboxRd.fourierL2 δ) ≤ ENNReal.ofReal (∫ x, δ x ^ 2) := by
  have hint := HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hδ
  have h1 : sobSqE t (HRS.PDE.ToolboxRd.fourierL2 δ) ≤
      ∫⁻ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ ^ 2 := by
    unfold sobSqE
    refine lintegral_mono fun ξ => ?_
    have : (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (Real.pi * ‖ξ‖)]) ht
    calc ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ t) * ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ ^ 2
        ≤ 1 * ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ ^ 2 := by
          gcongr
          exact ENNReal.ofReal_le_one.2 this
      _ = _ := one_mul _
  refine h1.trans (le_of_eq ?_)
  have e : ∀ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ₑ ^ 2 =
      ENNReal.ofReal (‖HRS.PDE.ToolboxRd.fourierL2 δ ξ‖ ^ 2) := by
    intro ξ; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ => by positivity),
    HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hδ]

end HRS.Commutator.Whole
