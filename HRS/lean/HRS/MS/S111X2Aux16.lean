import HRS.MS.S111X2Aux15
import HRS.MS.S111X2Aux14

/-!
# S11.1 X2, packet E03: classical fluctuation-dissipation `d/dr C_β(f_r,h_r) = 2β⁻¹ D(f_r,h_r)`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

section Aux

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

/-- The generator is autonomous for the stationary model. -/
theorem s111x2_gen_auto (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) (r : ℝ) :
    generatorW C r h = generatorW C 0 h := by
  have hg1 : ∀ y, ‖gradient h y‖ ≤ B1 := fun y => by rw [s111x2_norm_gradient]; exact H.d1 y
  funext x
  rw [HRS.MS.S111X1.gen_formula T.en H.smooth hg1 r x, HRS.MS.S111X1.gen_formula T.en H.smooth hg1 0 x]
  have hβ := T.en.hβ
  have hρ := T.pos x
  have h1 := T.en.grad r x
  have h2 := T.en.grad 0 x
  have hne : β * ρ x ≠ 0 := (mul_pos hβ hρ).ne'
  have : C.drift r x = C.drift 0 x := by
    have := h1.symm.trans h2
    exact smul_right_injective _ hne this
  rw [this]

theorem s111x2_lin_memLp (T : TD d s β ρ M C) (A : ℝ) :
    MemLp (fun x : Euc d => A * (1 + ‖x‖)) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  have hm : Measurable (fun x : Euc d => A * (1 + ‖x‖)) := (measurable_const.mul (measurable_const.add measurable_norm))
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  rw [tc2_integrable_nu T.prob]
  have hint : Integrable (fun x => 2 * A ^ 2 * ρ x + 2 * A ^ 2 * (‖x‖ ^ 2 * ρ x)) :=
    (T.en.K.int.const_mul _).add (T.mom2.const_mul _)
  refine hint.mono' ((T.en.K.meas.mul (hm.pow_const 2)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hρ0 := T.en.K.nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ0 (sq_nonneg _))]
  calc ρ x * (A * (1 + ‖x‖)) ^ 2 ≤ ρ x * (2 * A ^ 2 + 2 * A ^ 2 * ‖x‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hρ0
        nlinarith [sq_nonneg (A * (1 - ‖x‖))]
    _ = _ := by ring

theorem s111x2_dirichlet_symm (μ : Measure (Euc d)) (f h : Euc d → ℝ) :
    s111x2_dirichlet μ f h = s111x2_dirichlet μ h f := by
  unfold s111x2_dirichlet
  simp_rw [real_inner_comm]

theorem s111x2_dirichlet_bound (T : TD d s β ρ M C) {f h : Euc d → ℝ} {B1 B2 : ℝ}
    (hf : ∀ x, ‖fderiv ℝ f x‖ ≤ B1) (hh : ∀ x, ‖fderiv ℝ h x‖ ≤ B2) :
    |s111x2_dirichlet (HRS.Whole.withDensityReal ρ) f h| ≤ B1 * B2 := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  unfold s111x2_dirichlet
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hf 0)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := B1 * B2) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have g1 : ‖gradient f x‖ ≤ B1 := by rw [s111x2_norm_gradient]; exact hf x
    have g2 : ‖gradient h x‖ ≤ B2 := by rw [s111x2_norm_gradient]; exact hh x
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul g1 g2 (norm_nonneg _) hB1)
  · simp

end Aux

end HRS.MS.S111X2
