import HRS.MS.SA12X3N1F

/-!
# S.A.12 N1/N2 (SA12X3), part G: the uniform bound K1 and the convergence K2 for `γ_L ⋆ Q`, `∫ Q = 0`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_conv_periodic {L : ℝ} {γ : Euc d → ℝ} (hγ : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (Q : Euc d → ℝ) (x : Euc d) (k : Fin d → ℤ) :
    HRS.Whole.convFun γ Q (x + L • latticePt k) = HRS.Whole.convFun γ Q x := by
  unfold HRS.Whole.convFun
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show γ (x + L • latticePt k - u) * Q u = γ (x - u) * Q u
  have : x + L • latticePt k - u = (x - u) + L • latticePt k := by abel
  rw [this, hγ]

theorem sa12x3n_g_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {R ρ : ℝ} {Q : Euc d → ℝ}
    (hQs : tsupport Q ⊆ closedBall 0 R) {B : ℝ} (hB : ∀ u, |Q u| ≤ B) {x : Euc d} (hx : ‖x‖ + R ≤ ρ) :
    |HRS.Whole.convFun (rieszKernel d s) Q x| ≤
      B * ∫ w in closedBall (0 : Euc d) ρ, |rieszKernel d s w| := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hloc := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hint : IntegrableOn (fun w => |rieszKernel d s w|) (closedBall (0 : Euc d) ρ) volume :=
    (hloc.integrableOn_isCompact (isCompact_closedBall _ _)).abs
  have hpt : ∀ w, ‖rieszKernel d s w * Q (x - w)‖ ≤
      (closedBall (0 : Euc d) ρ).indicator (fun w => B * |rieszKernel d s w|) w := by
    intro w
    by_cases hw : w ∈ closedBall (0 : Euc d) ρ
    · rw [indicator_of_mem hw, Real.norm_eq_abs, abs_mul]
      calc |rieszKernel d s w| * |Q (x - w)| = |Q (x - w)| * |rieszKernel d s w| := mul_comm _ _
        _ ≤ B * |rieszKernel d s w| := mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
    · rw [indicator_of_notMem hw]
      have : Q (x - w) = 0 := by
        by_contra h
        apply hw
        have h1 := hQs (subset_tsupport Q h)
        rw [mem_closedBall, dist_zero_right] at h1
        rw [mem_closedBall, dist_zero_right]
        calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le _ _
          _ ≤ ρ := by linarith
      rw [this]; simp
  have hind : Integrable ((closedBall (0 : Euc d) ρ).indicator (fun w => B * |rieszKernel d s w|)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hint.const_mul B)
  have h := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hpt)
  have hconv : HRS.Whole.convFun (rieszKernel d s) Q x = ∫ w, rieszKernel d s w * Q (x - w) := by
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * Q (x - t)) x
    simp only [sub_sub_cancel] at h
    unfold HRS.Whole.convFun
    rw [← h]
  rw [hconv]
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [integral_indicator measurableSet_closedBall, integral_const_mul]

end HRS.MH.AdjointRd.Phase2SA12Construction
