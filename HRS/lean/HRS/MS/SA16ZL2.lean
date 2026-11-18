import HRS.MS.SA16ZL1

/-!
# S.A.16 (SA16Z) L2: the `L^p` bound of a singular integral near the origin by `‖∇f‖_p`

`sa16z_near_Lp`: for a finite-mass kernel `κ` and `f ∈ C_c^1`:
`∫⁻_x (∫⁻_z κ(z) D(x,z))^p ≤ (∫⁻ κ)^p ∫⁻ ‖Df‖^p`, `D(x,z) = ∫_0^1 ‖Df(x - t z)‖ dt`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L2
variable {d : ℕ}

/-- `D(x,z) = ∫_0^1 ‖Df(x - t z)‖ dt` -/
def sa16z_D (f : Euc d → ℝ) (x z : Euc d) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ

lemma sa16z_taylor_enorm {f : Euc d → ℝ} (hf : IsCcInfty f) (x z : Euc d) :
    ‖f (x - z) - f x‖ₑ ≤ ‖z‖ₑ * sa16z_D f x z := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by simp)
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  set g : ℝ → ℝ := fun t => f (x - t • z) with hg
  have hder : ∀ t : ℝ, HasDerivAt g (-fderiv ℝ f (x - t • z) z) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x - t • z) (-z) t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_sub x
    have h2 := (hd (x - t • z)).hasFDerivAt.comp_hasDerivAt t h1
    rw [map_neg] at h2
    exact h2
  have hcont : Continuous (fun t : ℝ => -fderiv ℝ f (x - t • z) z) := by
    have : Continuous (fun t : ℝ => x - t • z) := continuous_const.sub (continuous_id.smul continuous_const)
    exact ((hc.comp this).clm_apply continuous_const).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hcont.intervalIntegrable 0 1)
  have h01 : f (x - z) - f x = ∫ t in (0 : ℝ)..1, -fderiv ℝ f (x - t • z) z := by
    rw [hftc]; simp [hg]
  rw [h01, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  unfold sa16z_D
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_mono fun t => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_neg, ← Real.enorm_eq_ofReal_abs, mul_comm]
  exact ContinuousLinearMap.le_opENorm _ _

end L2

end HRS.Whole.AppendixA.Phase2SA16R
