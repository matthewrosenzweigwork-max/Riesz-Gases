import HRS.MS.SA16ZP1

/-!
# S.A.16 (SA16Y3) Lin1: linearity of `ψ ↦ P_a ψ` on `C_c^∞` (packet P7 iso, step (a))

`sa16y3_P_add`, `sa16y3_P_smul`: `P_a (φ + ψ) = P_a φ + P_a ψ`, `P_a (c φ) = c P_a φ` for `a` smooth, `φ, ψ ∈ C_c^∞`,
`0 ≤ s < d`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lin1
variable {d : ℕ} {s : ℝ}

lemma sa16y3_src_add {a φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) (i : Fin d) :
    sa16z_src a (φ + ψ) i = fun y => sa16z_src a φ i y + sa16z_src a ψ i y := by
  funext y
  simp only [sa16z_src]
  rw [fderiv_add (hφ.1.differentiable (by simp) y) (hψ.1.differentiable (by simp) y)]
  simp [mul_add]

lemma sa16y3_src_smul {a φ : Euc d → ℝ} (hφ : IsCcInfty φ) (c : ℝ) (i : Fin d) :
    sa16z_src a (c • φ) i = c • sa16z_src a φ i := by
  funext y
  simp only [sa16z_src, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_smul (hφ.1.differentiable (by simp) y)]
  simp [mul_left_comm]

lemma sa16y3_conv_smul (κ f : Euc d → ℝ) (c : ℝ) :
    convFun κ (c • f) = c • convFun κ f := by
  funext x
  simp only [convFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

theorem sa16y3_P_add (hs0 : 0 ≤ s) (hsd : s < d) {a φ ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    sa16z_P s a (φ + ψ) = sa16z_P s a φ + sa16z_P s a ψ := by
  funext x
  simp only [sa16z_P, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16y3_src_add hφ hψ i, sa16z_conv_add hs0 hsd (sa16z_src_cc ha hφ i) (sa16z_src_cc ha hψ i)]
  have h1 := sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hφ i)
  have h2 := sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hψ i)
  rw [fderiv_fun_add (h1.differentiable (by simp) x) (h2.differentiable (by simp) x)]
  rfl

theorem sa16y3_P_smul (hs0 : 0 ≤ s) (hsd : s < d) {a φ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hφ : IsCcInfty φ) (c : ℝ) :
    sa16z_P s a (c • φ) = c • sa16z_P s a φ := by
  funext x
  simp only [sa16z_P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16y3_src_smul hφ c i, sa16y3_conv_smul]
  have h1 := sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hφ i)
  rw [fderiv_const_smul (h1.differentiable (by simp) x)]
  rfl

end Lin1

end HRS.Whole.AppendixA.Phase2SA16R
