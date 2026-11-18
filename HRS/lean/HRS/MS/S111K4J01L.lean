import HRS.MS.S111K4J01K

/-!
# S11.1 / J01 piece: real norm bounds of the drift and covariance interval maps in the `L¹` norm (S11K4)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem q_norm_eq {H : ℝ} (q : TimeCoeff H) :
    ‖q‖ = ∫ v in Set.Icc (0 : ℝ) H, ‖(q : ℝ → Coeff) v‖ := by
  exact MeasureTheory.L1.norm_eq_integral_norm q

theorem q_integrable {H : ℝ} (q : TimeCoeff H) :
    Integrable (fun v => ‖(q : ℝ → Coeff) v‖) (volume.restrict (Set.Icc (0 : ℝ) H)) :=
  (Lp.memLp q |>.integrable le_rfl).norm

/-- `∫_{(a,b]} w ‖q‖ ≤ ∫_{(a,b]} ‖q‖ ≤ ‖q‖` for a weight `0 ≤ w ≤ 1`. -/
theorem weighted_int_le {H a b' : ℝ} (ha : 0 ≤ a) (hb : b' ≤ H) (q : TimeCoeff H) {w : ℝ → ℝ}
    (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1) (hwm : Measurable w) :
    ∫ v in Set.Ioc a b', w v * ‖(q : ℝ → Coeff) v‖ ≤ ‖q‖ := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) H := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  have hI : IntegrableOn (fun v => ‖(q : ℝ → Coeff) v‖) (Set.Icc (0 : ℝ) H) volume := q_integrable q
  have hIo : IntegrableOn (fun v => ‖(q : ℝ → Coeff) v‖) (Set.Ioc a b') volume := hI.mono_set hsub
  have hwI : Integrable (fun v => w v * ‖(q : ℝ → Coeff) v‖) (volume.restrict (Set.Ioc a b')) := by
    refine Integrable.mono' hIo (hwm.aemeasurable.mul (Lp.stronglyMeasurable q).norm.measurable.aemeasurable).aestronglyMeasurable ?_
    refine Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 v) (norm_nonneg _))]
    calc w v * ‖(q : ℝ → Coeff) v‖ ≤ 1 * ‖(q : ℝ → Coeff) v‖ :=
          mul_le_mul_of_nonneg_right (hw1 v) (norm_nonneg _)
      _ = _ := one_mul _
  rw [q_norm_eq]
  calc ∫ v in Set.Ioc a b', w v * ‖(q : ℝ → Coeff) v‖ ≤ ∫ v in Set.Ioc a b', ‖(q : ℝ → Coeff) v‖ :=
        integral_mono hwI hIo fun v => by
          calc w v * ‖(q : ℝ → Coeff) v‖ ≤ 1 * ‖(q : ℝ → Coeff) v‖ :=
                mul_le_mul_of_nonneg_right (hw1 v) (norm_nonneg _)
            _ = _ := one_mul _
    _ ≤ ∫ v in Set.Icc (0 : ℝ) H, ‖(q : ℝ → Coeff) v‖ :=
        setIntegral_mono_set hI (Eventually.of_forall fun v => norm_nonneg _) (Eventually.of_forall hsub)

end HRS.MS.S111K4J01
