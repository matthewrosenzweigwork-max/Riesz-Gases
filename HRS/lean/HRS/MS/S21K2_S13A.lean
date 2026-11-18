import HRS.Whole.Basic

/-!
# S21K2 S13A -- marginal `L²` bound for a pair kernel (R26-T3.S13, first step)

If `k ∈ L²(μ ⊗ μ)` for a probability measure `μ`, then the marginal `x ↦ ∫ k(x,y) dμ(y)` lies in `L²(μ)`.
Pointwise Jensen (variance nonnegativity) on the a.e. sections, then integrability of the square of the marginal.
Helper prefix `s21k2_s13_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory
noncomputable section
namespace HRS.MS.R26T3

theorem s21k2_s13_marg_memLp {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {k : HRS.Euc d → HRS.Euc d → ℝ}
    (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun x => ∫ y, k x y ∂μ) 2 μ := by
  have hI : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2 ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).1 hk
  have hL1 : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) (μ.prod μ) :=
    hk.integrable (by norm_num)
  have hsec1 : ∀ᵐ x ∂μ, Integrable (fun y => k x y) μ := hL1.prod_right_ae
  have hsec2 : ∀ᵐ x ∂μ, Integrable (fun y => k x y ^ 2) μ := hI.prod_right_ae
  have hjen : ∀ᵐ x ∂μ, (∫ y, k x y ∂μ) ^ 2 ≤ ∫ y, k x y ^ 2 ∂μ := by
    filter_upwards [hsec1, hsec2] with x h1 h2
    have hX : MemLp (fun y => k x y) 2 μ := (memLp_two_iff_integrable_sq h1.1).2 h2
    have hv := variance_nonneg (fun y => k x y) μ
    rw [variance_eq_sub hX] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  have hF : Integrable (fun x => ∫ y, k x y ^ 2 ∂μ) μ := hI.integral_prod_left
  have hA : Integrable (fun x => ∫ y, k x y ∂μ) μ := hL1.integral_prod_left
  have hsq : Integrable (fun x => (∫ y, k x y ∂μ) ^ 2) μ :=
    hF.mono' (hA.1.pow 2) (by
      filter_upwards [hjen] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx)
  exact (memLp_two_iff_integrable_sq hA.1).2 hsq

end HRS.MS.R26T3
