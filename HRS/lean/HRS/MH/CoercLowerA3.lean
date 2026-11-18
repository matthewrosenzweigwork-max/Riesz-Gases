import Mathlib
import HRS.Whole.Basic
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerA1
import HRS.MH.CoercLowerA2

/-!
# CoercLower, packets P11 (`gauss_Qform_eq`) and P12 (`Qform_gauss_nonneg`).

Statements are copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

private theorem cla3_integrable_rho {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

private theorem cla3_gaussK_meas {t : ℝ} : Measurable (gaussK t : Euc d → ℝ) := by
  unfold gaussK
  fun_prop

/-- `z ↦ ∫ y, e^{-2t‖y-z‖²} ρ y` is measurable. -/
private theorem cla3_U_meas {t : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    Measurable (fun z : Euc d => ∫ y, gaussK (2 * t) (y - z) * ρ y) := by
  have hρm := hρ.measurable
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla3_gaussK_meas
  have : StronglyMeasurable (Function.uncurry fun (z y : Euc d) => gaussK (2 * t) (y - z) * ρ y) := by
    have : Measurable (Function.uncurry fun (z y : Euc d) => gaussK (2 * t) (y - z) * ρ y) := by
      show Measurable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
      fun_prop
    exact this.stronglyMeasurable
  exact (this.integral_prod_right (ν := (volume : Measure (Euc d)))).measurable

/-- `z ↦ ∫ y, e^{-2t‖y-z‖²} ρ y` is integrable. -/
private theorem cla3_U_integrable {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable (fun z : Euc d => ∫ y, gaussK (2 * t) (y - z) * ρ y) := by
  have ht2 : 0 < 2 * t := by linarith
  have hρi := cla3_integrable_rho hρ
  have hρm := hρ.measurable
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla3_gaussK_meas
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) ht2).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) ht2).2.1 w).1
  have hm : AEStronglyMeasurable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
      (volume.prod volume) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hb : Integrable (fun p : Euc d × Euc d => gaussK (2 * t) (p.2 - p.1) * ρ p.2)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hm]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · show Integrable (fun z : Euc d => gaussK (2 * t) (y - z) * ρ y) volume
      exact ((gaussK_basic (d := d) ht2).2.2.1.comp_sub_left y).mul_const _
    · show Integrable (fun y : Euc d => ∫ z : Euc d, ‖gaussK (2 * t) (y - z) * ρ y‖) volume
      have hc : ∀ y : Euc d, ∫ z, ‖gaussK (2 * t) (y - z) * ρ y‖ =
          (∫ w : Euc d, gaussK (2 * t) w) * ρ y := by
        intro y
        have : ∀ z : Euc d, ‖gaussK (2 * t) (y - z) * ρ y‖ = gaussK (2 * t) (y - z) * ρ y :=
          fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _).le (hρ.nonneg y))]
        simp_rw [this]
        rw [integral_mul_const, integral_sub_left_eq_self (fun w : Euc d => gaussK (2 * t) w) volume y]
      simp_rw [hc]
      exact hρi.const_mul _
  exact hb.integral_prod_left

/-- Bounds `0 ≤ U ≤ 1`. -/
private theorem cla3_U_bounds {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (z : Euc d) :
    0 ≤ ∫ y, gaussK (2 * t) (y - z) * ρ y ∧ ∫ y, gaussK (2 * t) (y - z) * ρ y ≤ 1 := by
  have ht2 : 0 < 2 * t := by linarith
  have hρi := cla3_integrable_rho hρ
  have hρm := hρ.measurable
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla3_gaussK_meas
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) ht2).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) ht2).2.1 w).1
  refine ⟨integral_nonneg fun y => mul_nonneg (hpos _).le (hρ.nonneg y), ?_⟩
  have hi : Integrable (fun y => gaussK (2 * t) (y - z) * ρ y) := by
    refine hρi.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (by fun_prop : Measurable (fun y => gaussK (2 * t) (y - z) * ρ y)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _).le (hρ.nonneg y))]
      have := hle (y - z); have := hρ.nonneg y
      nlinarith
  calc ∫ y, gaussK (2 * t) (y - z) * ρ y ≤ ∫ y, ρ y := integral_mono hi hρi fun y => by
        have := hle (y - z); have := hρ.nonneg y
        show gaussK (2 * t) (y - z) * ρ y ≤ ρ y
        nlinarith
    _ = 1 := hρ.integral_one

/-- P11: `Qform` of a Gaussian is a multiple of `∫ u²`. -/
theorem gauss_Qform_eq {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) :
    (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) * Qform (gaussK t) X ρ = ∫ z, (gaussU t X ρ z) ^ 2 := by
  have ht2 : 0 < 2 * t := by linarith
  have hGm : Measurable (gaussK (2 * t) : Euc d → ℝ) := cla3_gaussK_meas
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) ht2).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) ht2).2.1 w).1
  set c : ℝ := (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) with hc
  set U : Euc d → ℝ := fun z => ∫ y, gaussK (2 * t) (y - z) * ρ y with hU
  have hUm : Measurable U := cla3_U_meas hρ
  have hUi : Integrable U := cla3_U_integrable ht hρ
  have hU0 : ∀ z, 0 ≤ U z := fun z => (cla3_U_bounds ht hρ z).1
  have hU1 : ∀ z, U z ≤ 1 := fun z => (cla3_U_bounds ht hρ z).2
  set G : Fin N → Euc d → ℝ := fun i z => gaussK (2 * t) (X i - z) with hG
  have hGi : ∀ i, Integrable (G i) := fun i =>
    (gaussK_basic (d := d) ht2).2.2.1.comp_sub_left (X i)
  have hGmi : ∀ i, Measurable (G i) := fun i => by simp only [hG]; fun_prop
  have hG0 : ∀ i z, 0 < G i z := fun i z => hpos _
  have hG1 : ∀ i z, G i z ≤ 1 := fun i z => hle _
  -- integrability of the pieces
  have iGG : ∀ i j, Integrable (fun z => G i z * G j z) := fun i j => by
    refine (hGi i).mono' ((hGmi i).mul (hGmi j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hG0 i z) (hG0 j z))]
    have := hG0 i z; have := hG0 j z; have := hG1 j z
    nlinarith
  have iGU : ∀ i, Integrable (fun z => G i z * U z) := fun i => by
    refine (hGi i).mono' ((hGmi i).mul hUm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hG0 i z).le (hU0 z))]
    have := hG0 i z; have := hU0 z; have := hU1 z
    nlinarith
  have iUU : Integrable (fun z => U z ^ 2) := by
    refine hUi.mono' (hUm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hU0 z; have := hU1 z
    nlinarith
  -- the three integrals
  have eGG : ∀ i j, ∫ z, G i z * G j z = c * gaussK t (X i - X j) := fun i j =>
    gauss_overlap ht (X i) (X j)
  have eGU : ∀ i, ∫ z, G i z * U z = c * HRS.Whole.convFun (gaussK t) ρ (X i) := fun i =>
    gauss_cross ht hρ (X i)
  have eUU : ∫ z, U z ^ 2 = c * energyDens (gaussK t) ρ := gauss_square ht hρ
  set a : Euc d → ℝ := fun z => (1 / (N : ℝ)) * ∑ i, G i z with ha
  have iaa : Integrable (fun z => a z ^ 2) := by
    have : (fun z => a z ^ 2) = fun z => (1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j, G i z * G j z := by
      funext z
      simp only [ha]
      rw [mul_pow, sq (∑ i, G i z), Finset.sum_mul_sum]
    rw [this]
    exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iGG i j).const_mul _
  have iab : Integrable (fun z => a z * U z) := by
    have : (fun z => a z * U z) = fun z => (1 / (N : ℝ)) * ∑ i, G i z * U z := by
      funext z
      simp only [ha]
      rw [mul_assoc, Finset.sum_mul]
    rw [this]
    exact (integrable_finsetSum _ fun i _ => iGU i).const_mul _
  have eaa : ∫ z, a z ^ 2 = c * ((1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j, gaussK t (X i - X j)) := by
    have : (fun z => a z ^ 2) = fun z => (1 / (N : ℝ)) ^ 2 * ∑ i, ∑ j, G i z * G j z := by
      funext z
      simp only [ha]
      rw [mul_pow, sq (∑ i, G i z), Finset.sum_mul_sum]
    rw [this, integral_const_mul, integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => iGG i j]
    simp_rw [integral_finsetSum _ fun j _ => iGG _ j, eGG]
    simp_rw [← Finset.mul_sum]
    ring
  have eab : ∫ z, a z * U z = c * ((1 / (N : ℝ)) * ∑ i, HRS.Whole.convFun (gaussK t) ρ (X i)) := by
    have : (fun z => a z * U z) = fun z => (1 / (N : ℝ)) * ∑ i, G i z * U z := by
      funext z
      simp only [ha]
      rw [mul_assoc, Finset.sum_mul]
    rw [this, integral_const_mul, integral_finsetSum _ fun i _ => iGU i]
    simp_rw [eGU, ← Finset.mul_sum]
    ring
  have hu : ∀ z, gaussU t X ρ z = a z - U z := fun z => rfl
  have e1 : (fun z => gaussU t X ρ z ^ 2) = fun z => (a z ^ 2 - 2 * (a z * U z)) + U z ^ 2 := by
    funext z; rw [hu]; ring
  have i2 : Integrable (fun z => 2 * (a z * U z)) := iab.const_mul 2
  have i3 : Integrable (fun z => a z ^ 2 - 2 * (a z * U z)) := iaa.sub i2
  rw [e1, integral_add i3 iUU, integral_sub iaa i2,
    integral_const_mul, eaa, eab, eUU]
  unfold Qform
  have hNN : (1 / (N : ℝ)) ^ 2 = 1 / (N : ℝ) ^ 2 := by rw [one_div, one_div, inv_pow]
  rw [hNN]
  field_simp

/-- P12: Step 1, Gaussian positive definiteness. -/
theorem Qform_gauss_nonneg {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) : 0 ≤ Qform (gaussK t) X ρ := by
  have h := gauss_Qform_eq ht hρ hN X
  have hc : 0 < (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) := by positivity
  have h2 : 0 ≤ ∫ z, (gaussU t X ρ z) ^ 2 := integral_nonneg fun z => sq_nonneg _
  rw [← h] at h2
  exact nonneg_of_mul_nonneg_right h2 hc

end HRS.MH.CoercLower
