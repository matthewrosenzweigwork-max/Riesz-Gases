import Mathlib
import HRS.Whole.Basic
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerA1

/-!
# CoercLower, packets P09 (`gauss_cross`) and P10 (`gauss_square`).

Statements are copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

private theorem cla2_integrable_rho {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

private theorem cla2_gaussK_meas {t : ℝ} : Measurable (gaussK t : Euc d → ℝ) := by
  unfold gaussK
  fun_prop

private theorem cla2_gaussK_comp_integrable {t : ℝ} (ht : 0 < t) (x : Euc d) :
    Integrable (fun z : Euc d => gaussK t (x - z)) :=
  (gaussK_basic (d := d) ht).2.2.1.comp_sub_left x

/-- P09: cross term. -/
theorem gauss_cross {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (x : Euc d) :
    ∫ z, gaussK (2 * t) (x - z) * ∫ y, gaussK (2 * t) (y - z) * ρ y =
      (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * HRS.Whole.convFun (gaussK t) ρ x := by
  have ht2 : 0 < 2 * t := by linarith
  have hρi := cla2_integrable_rho hρ
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla2_gaussK_meas
  have hρm := hρ.measurable
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) ht2).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) ht2).2.1 w).1
  have hint : Integrable (fun p : Euc d × Euc d =>
      gaussK (2 * t) (x - p.1) * (gaussK (2 * t) (p.2 - p.1) * ρ p.2)) (volume.prod volume) := by
    have hb : Integrable (fun p : Euc d × Euc d => gaussK (2 * t) (x - p.1) * ρ p.2)
        (volume.prod volume) :=
      Integrable.mul_prod (f := fun z : Euc d => gaussK (2 * t) (x - z)) (g := ρ)
        (cla2_gaussK_comp_integrable ht2 x) hρi
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have : Measurable (fun p : Euc d × Euc d =>
          gaussK (2 * t) (x - p.1) * (gaussK (2 * t) (p.2 - p.1) * ρ p.2)) := by fun_prop
      exact this.aestronglyMeasurable
    · simp only [norm_mul, Real.norm_eq_abs]
      rw [abs_of_pos (hpos _), abs_of_pos (hpos _), abs_of_nonneg (hρ.nonneg _)]
      have h1 := hle (p.2 - p.1)
      have h2 := hpos (x - p.1)
      have h3 := hρ.nonneg p.2
      have : gaussK (2 * t) (p.2 - p.1) * ρ p.2 ≤ ρ p.2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this h2.le
  have step1 : ∀ z : Euc d, gaussK (2 * t) (x - z) * ∫ y, gaussK (2 * t) (y - z) * ρ y =
      ∫ y, gaussK (2 * t) (x - z) * (gaussK (2 * t) (y - z) * ρ y) := fun z =>
    (integral_const_mul _ _).symm
  simp_rw [step1]
  rw [integral_integral_swap hint]
  have step2 : ∀ y : Euc d, ∫ z, gaussK (2 * t) (x - z) * (gaussK (2 * t) (y - z) * ρ y) =
      (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * (gaussK t (x - y) * ρ y) := by
    intro y
    have := gauss_overlap (d := d) ht x y
    simp_rw [← mul_assoc]
    rw [integral_mul_const, this, mul_assoc]
  simp_rw [step2]
  rw [integral_const_mul]
  rfl

/-- P10: square term. -/
theorem gauss_square {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    ∫ z, (∫ y, gaussK (2 * t) (y - z) * ρ y) ^ 2 =
      (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * energyDens (gaussK t) ρ := by
  have ht2 : 0 < 2 * t := by linarith
  have hρi := cla2_integrable_rho hρ
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla2_gaussK_meas
  have hρm := hρ.measurable
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) ht2).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) ht2).2.1 w).1
  set U : Euc d → ℝ := fun z => ∫ y, gaussK (2 * t) (y - z) * ρ y with hU
  have hUm : Measurable U := by
    have : StronglyMeasurable (Function.uncurry fun (z y : Euc d) => gaussK (2 * t) (y - z) * ρ y) := by
      have : Measurable (Function.uncurry fun (z y : Euc d) => gaussK (2 * t) (y - z) * ρ y) := by
        show Measurable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
        fun_prop
      exact this.stronglyMeasurable
    exact (this.integral_prod_right (ν := (volume : Measure (Euc d)))).measurable
  have hU0 : ∀ z, 0 ≤ U z := fun z =>
    integral_nonneg fun y => mul_nonneg (hpos _).le (hρ.nonneg y)
  have hU1 : ∀ z, U z ≤ 1 := by
    intro z
    have hi : Integrable (fun y => gaussK (2 * t) (y - z) * ρ y) := by
      refine hρi.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact (by fun_prop : Measurable (fun y => gaussK (2 * t) (y - z) * ρ y)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _).le (hρ.nonneg y))]
        have := hle (y - z); have := hρ.nonneg y
        nlinarith
    calc U z ≤ ∫ y, ρ y := integral_mono hi hρi fun y => by
          have := hle (y - z); have := hρ.nonneg y
          show gaussK (2 * t) (y - z) * ρ y ≤ ρ y
          nlinarith
      _ = 1 := hρ.integral_one
  have hint : Integrable (fun p : Euc d × Euc d =>
      U p.1 * (gaussK (2 * t) (p.2 - p.1) * ρ p.2)) (volume.prod volume) := by
    have hb : Integrable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
        (volume.prod volume) := by
      have hm : AEStronglyMeasurable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
          (volume.prod volume) := (by fun_prop : Measurable _).aestronglyMeasurable
      rw [integrable_prod_iff' hm]
      refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
      · show Integrable (fun z : Euc d => gaussK (2 * t) (y - z) * ρ y) volume
        exact (cla2_gaussK_comp_integrable ht2 y).mul_const _
      · show Integrable (fun y : Euc d => ∫ z : Euc d, ‖gaussK (2 * t) (y - z) * ρ y‖) volume
        have hc : ∀ y : Euc d, ∫ z, ‖gaussK (2 * t) (y - z) * ρ y‖ =
            (∫ w : Euc d, gaussK (2 * t) w) * ρ y := by
          intro y
          have : ∀ z : Euc d, ‖gaussK (2 * t) (y - z) * ρ y‖ = gaussK (2 * t) (y - z) * ρ y := fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _).le (hρ.nonneg y))]
          simp_rw [this]
          rw [integral_mul_const, integral_sub_left_eq_self (fun w : Euc d => gaussK (2 * t) w) volume y]
        simp_rw [hc]
        exact hρi.const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Measurable (fun p : Euc d × Euc d =>
          U p.1 * (gaussK (2 * t) (p.2 - p.1) * ρ p.2))).aestronglyMeasurable
    · simp only [norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (hU0 _), abs_of_pos (hpos _), abs_of_nonneg (hρ.nonneg _)]
      have h2 : 0 ≤ gaussK (2 * t) (p.2 - p.1) * ρ p.2 :=
        mul_nonneg (hpos _).le (hρ.nonneg _)
      nlinarith [hU1 p.1]
  have step1 : ∀ z : Euc d, (U z) ^ 2 = ∫ y, U z * (gaussK (2 * t) (y - z) * ρ y) := by
    intro z
    rw [integral_const_mul, sq]
  have e1 : (fun z : Euc d => (∫ y, gaussK (2 * t) (y - z) * ρ y) ^ 2) =
      fun z => ∫ y, U z * (gaussK (2 * t) (y - z) * ρ y) := funext step1
  rw [e1, integral_integral_swap hint]
  have step2 : ∀ y : Euc d, ∫ z, U z * (gaussK (2 * t) (y - z) * ρ y) =
      ρ y * ((Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * HRS.Whole.convFun (gaussK t) ρ y) := by
    intro y
    rw [← gauss_cross ht hρ y, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show U z * (gaussK (2 * t) (y - z) * ρ y) = ρ y * (gaussK (2 * t) (y - z) * U z)
    ring
  simp_rw [step2]
  unfold energyDens
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ρ y * ((Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * HRS.Whole.convFun (gaussK t) ρ y) = _
  ring

end HRS.MH.CoercLower
