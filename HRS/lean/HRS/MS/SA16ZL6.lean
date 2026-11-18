import HRS.MS.SA16ZL5

/-!
# S.A.16 (SA16Z) L6: the `W^{1,p} → L^p` bound of the first-kernel principal value (`1 < θ < 2`)

`sa16z_pv_W1p`: `‖pvOdd d θ (u ↦ u_i) f‖_p ≤ C (‖f‖_p + ‖∇f‖_p)` for `f ∈ C_c^∞`, `p > 1`,
with `C = C(d,θ,i)` independent of `f` and `p`-dependence only through the statement.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L6
variable {d : ℕ}

open HRS.CZ.Pv in
/-- the near kernel `‖K(z)‖ ‖z‖ 1_{|z| ≤ 1}` -/
def sa16z_kap (d : ℕ) (θ : ℝ) (i : Fin d) (z : Euc d) : ℝ≥0∞ :=
  (closedBall (0 : Euc d) 1).indicator (fun z => ‖pvK d θ (fun u : Euc d => u i) z‖ₑ * ‖z‖ₑ) z

open HRS.CZ.Pv in
/-- the far kernel `‖K(z)‖ 1_{|z| > 1}` -/
def sa16z_kfar (d : ℕ) (θ : ℝ) (i : Fin d) (z : Euc d) : ℝ≥0∞ :=
  {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖pvK d θ (fun u : Euc d => u i) z‖ₑ) z

open HRS.CZ.Pv in
lemma sa16z_kap_meas (hd : 1 ≤ d) (θ : ℝ) (i : Fin d) : Measurable (sa16z_kap d θ i) := by
  unfold sa16z_kap
  have h1 : Measurable fun z : Euc d => ‖pvK d θ (fun u : Euc d => u i) z‖ₑ :=
    (pvK_measurable (isPvKernel_coord i) θ).enorm
  have h2 : Measurable fun z : Euc d => ‖z‖ₑ := measurable_enorm
  exact (h1.mul h2).indicator measurableSet_closedBall

open HRS.CZ.Pv in
lemma sa16z_kfar_meas (θ : ℝ) (i : Fin d) : Measurable (sa16z_kfar d θ i) := by
  unfold sa16z_kfar
  exact ((pvK_measurable (isPvKernel_coord i) θ).enorm).indicator
    (measurableSet_lt measurable_const measurable_norm)

open HRS.CZ.Pv in
theorem sa16z_pv_pointwise (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {f : Euc d → ℝ}
    (hf : IsCcInfty f) (i : Fin d) (x : Euc d) :
    ‖pvOdd d θ (fun u : Euc d => u i) f x‖ₑ ≤
      (∫⁻ z, sa16z_kap d θ i z * sa16z_D f x z) + ∫⁻ z, sa16z_kfar d θ i z * ‖f (x - z)‖ₑ := by
  have hθ0 : 0 < θ := by linarith
  have hK := isPvKernel_coord (d := d) i
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  obtain ⟨Cb, hCb⟩ := hc.bounded_above_of_compact_support (hf.2.fderiv ℝ)
  have hLip : ∀ y, ‖fderiv ℝ f y‖₊ ≤ Cb.toNNReal := fun y => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hCb y).trans (Real.le_coe_toNNReal Cb)
  have hfint : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hfar := pvK_far_integrable_of_integrable hd hθ0 hK hfint x
  rw [pvOdd_eq_of_C1 hd hθ0 hθ2 hK (hf.1.of_le (by simp)) hLip x hfar]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have : ∫⁻ z, sa16z_kap d θ i z * sa16z_D f x z =
        ∫⁻ z in closedBall (0 : Euc d) 1, ‖pvK d θ (fun u : Euc d => u i) z‖ₑ * (‖z‖ₑ * sa16z_D f x z) := by
      rw [← lintegral_indicator measurableSet_closedBall]
      refine lintegral_congr fun z => ?_
      unfold sa16z_kap
      by_cases hz : z ∈ closedBall (0 : Euc d) 1
      · simp only [indicator_of_mem hz]; ring
      · simp [indicator_of_notMem hz]
    rw [this]
    refine lintegral_mono fun z => ?_
    rw [enorm_mul]
    gcongr
    exact sa16z_taylor_enorm hf x z
  · refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hS : MeasurableSet {z : Euc d | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    have : ∫⁻ z, sa16z_kfar d θ i z * ‖f (x - z)‖ₑ =
        ∫⁻ z in {z : Euc d | 1 < ‖z‖}, ‖pvK d θ (fun u : Euc d => u i) z‖ₑ * ‖f (x - z)‖ₑ := by
      rw [← lintegral_indicator hS]
      refine lintegral_congr fun z => ?_
      unfold sa16z_kfar
      by_cases hz : z ∈ {z : Euc d | 1 < ‖z‖}
      · simp only [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]
    rw [this]
    exact le_of_eq (lintegral_congr fun z => by rw [enorm_mul])

end L6

end HRS.Whole.AppendixA.Phase2SA16R
