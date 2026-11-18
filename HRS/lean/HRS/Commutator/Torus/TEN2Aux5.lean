import HRS.Commutator.Torus.TEN2Aux4

/-!
# Torus energy layer (packet T-EN2), helper part 5: `‖f_η^𝕋‖_{L^q(𝕋^d)} ≲ η^{d/q-s}`

Prefix `ten2_`.  Dilation of the `L^q(ℝ^d)` norm, the bound for `f_η ∘ centeredRep`, and the periodised,
mean-corrected kernel `f_η^𝕋`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

theorem ten2_eLpNorm_dilate {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (F : Euc d → ℝ)
    (hF : Measurable F) (hη : 0 < η) :
    eLpNorm (fun y : Euc d => F (η⁻¹ • y)) q volume ≤
      ENNReal.ofReal (η ^ ((d : ℝ) / q.toReal)) * eLpNorm F q volume := by
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hmap : Measure.map (fun y : Euc d => η⁻¹ • y) (volume : Measure (Euc d)) =
      ENNReal.ofReal (η ^ d) • volume := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hη.ne'), finrank_euclideanSpace_fin]
    congr 2
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hη d)]
  have hmeas : Measurable fun y : Euc d => ‖F y‖ₑ ^ q.toReal := hF.enorm.pow_const _
  have hint : ∫⁻ y : Euc d, ‖F (η⁻¹ • y)‖ₑ ^ q.toReal =
      ENNReal.ofReal (η ^ d) * ∫⁻ y : Euc d, ‖F y‖ₑ ^ q.toReal := by
    rw [← lintegral_map hmeas (measurable_const_smul η⁻¹), hmap, lintegral_smul_measure]
    rfl
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun y : Euc d => F (η⁻¹ • y)) hq0 hqt (hF.comp (measurable_const_smul η⁻¹)).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hF.aestronglyMeasurable, hint,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  refine le_of_eq (congrArg₂ _ ?_ rfl)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hη.le]
  congr 2
  ring

theorem ten2_eLpNorm_fTrunc_scale {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hη : 0 < η) :
    eLpNorm (Whole.fTrunc s η : Euc d → ℝ) q volume ≤
      ENNReal.ofReal (η ^ ((d : ℝ) / q.toReal - s)) * eLpNorm (Whole.fTrunc s 1 : Euc d → ℝ) q volume := by
  have hfun : (Whole.fTrunc s η : Euc d → ℝ) =
      (η ^ (-s)) • (fun y : Euc d => (Whole.fTrunc s 1 : Euc d → ℝ) (η⁻¹ • y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    exact tpos_fTrunc_scale hη y
  have h1 := eLpNorm_const_smul_le (μ := (volume : Measure (Euc d))) (p := q) (c := η ^ (-s))
    (f := fun y : Euc d => (Whole.fTrunc s 1 : Euc d → ℝ) (η⁻¹ • y))
  have h2 := ten2_eLpNorm_dilate (d := d) (η := η) hq0 hqt (Whole.fTrunc s 1 : Euc d → ℝ)
    (tpos_fTrunc_measurable one_pos) hη
  rw [hfun]
  refine h1.trans ?_
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg hη.le _)]
  calc ENNReal.ofReal (η ^ (-s)) * eLpNorm (fun y : Euc d => (Whole.fTrunc s 1 : Euc d → ℝ) (η⁻¹ • y)) q volume
      ≤ ENNReal.ofReal (η ^ (-s)) *
        (ENNReal.ofReal (η ^ ((d : ℝ) / q.toReal)) * eLpNorm (Whole.fTrunc s 1 : Euc d → ℝ) q volume) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (η ^ ((d : ℝ) / q.toReal - s)) * eLpNorm (Whole.fTrunc s 1 : Euc d → ℝ) q volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _), ← Real.rpow_add hη]
        congr 3
        ring

theorem ten2_eLpNorm_cr {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hη : 0 < η) :
    eLpNorm (fun x : Torus d => (Whole.fTrunc s η : Euc d → ℝ) (KernelGrad.centeredRep x)) q volume ≤
      eLpNorm (Whole.fTrunc s η : Euc d → ℝ) q volume := by
  have hmeas : Measurable fun y : Euc d => ‖(Whole.fTrunc s η : Euc d → ℝ) y‖ₑ ^ q.toReal :=
    (tpos_fTrunc_measurable hη).enorm.pow_const _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (f := fun x : Torus d => (Whole.fTrunc s η : Euc d → ℝ) (KernelGrad.centeredRep x)) hq0 hqt
      ((tpos_fTrunc_measurable hη).comp ten2_cr_measurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (tpos_fTrunc_measurable hη).aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow (ten2_lintegral_cr_le _ hmeas) (by positivity)

end HRS.Commutator.TorusNote
