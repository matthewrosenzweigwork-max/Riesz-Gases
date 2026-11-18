import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.Whole.MovtrAux2
import HRS.MS.MovForceAux6

/-!
# S6.7 nonlinear breakdown, packet 14A: local C1 cancellation integrability

`s67bd_near_integrable`: for `h ∈ C¹` the cancelled near-field integrand
`y ↦ (h y - h x) ∇g(x - y) 1_{|x-y| ≤ 1/4}` is integrable; mean value bound on the closed ball
`B(x, 1/4)` gives the majorant `const * |x - y|^{-s}`, locally integrable as `s < d`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_near (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (x y : Euc d) : Euc d :=
  if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • rieszKernelGrad d s (x - y) else 0

theorem s67bd_near_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) :
    ∀ x, Integrable (s67bd_near d s h x) volume := by
  intro x
  have hd1 : 1 ≤ d := by omega
  -- derivative bound on the closed ball
  obtain ⟨L, hL⟩ := (isCompact_closedBall x (1 / 4 : ℝ)).exists_bound_of_continuousOn
    (hh.continuous_fderiv one_ne_zero).continuousOn
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL x (Metric.mem_closedBall_self (by norm_num)))
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  -- local majorant
  set K : Euc d → ℝ := Set.indicator (Metric.ball (0 : Euc d) (1 / 2)) (fun z => ‖z‖ ^ (-s)) with hK
  have hKint : Integrable K volume := by
    rw [hK, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : Euc d => ‖z‖ ^ (-s))
      (C := 1) (α := s) (r := 1 / 2) (by rw [finrank_euclideanSpace_fin]; exact hd1)
      (by rw [finrank_euclideanSpace_fin]; exact hsd) (Eventually.of_forall fun z => ?_)
      (measurable_norm.pow_const _).aestronglyMeasurable
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  have hKnn : ∀ z, 0 ≤ K z := fun z => by
    rw [hK]; exact Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg w) _) z
  have hmajor : Integrable (fun y : Euc d => (movtr_sigma s * L) * K (x - y)) volume :=
    ((integrable_comp_sub_left K x).2 hKint).const_mul _
  -- measurability
  have hmeas : AEStronglyMeasurable (s67bd_near d s h x) volume := by
    have hm : Measurable (s67bd_near d s h x) := by
      unfold s67bd_near
      refine Measurable.ite (measurableSet_le (measurable_const.sub measurable_id).norm
        measurable_const) ?_ measurable_const
      exact ((hh.continuous.measurable.sub measurable_const).smul
        ((movtr_rieszKernelGrad_measurable s).comp (measurable_const.sub measurable_id)))
    exact hm.aestronglyMeasurable
  refine hmajor.mono' hmeas (Eventually.of_forall fun y => ?_)
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · have hnear : s67bd_near d s h x y = (h y - h x) • rieszKernelGrad d s (x - y) := by
      simp only [s67bd_near, hy, ↓reduceIte]
    rw [hnear]
    by_cases hz : x - y = 0
    · have : y = x := by rw [sub_eq_zero] at hz; exact hz.symm
      subst this
      simp only [sub_self, zero_smul, norm_zero]
      exact mul_nonneg (mul_nonneg hσ hL0) (hKnn _)
    · have hzpos : 0 < ‖x - y‖ := norm_pos_iff.2 hz
      have hmv : ‖h y - h x‖ ≤ L * ‖y - x‖ := by
        refine (convex_closedBall x (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (fun w _ => (hh.differentiable one_ne_zero) w) (fun w hw => hL w hw)
          (Metric.mem_closedBall_self (by norm_num)) ?_
        rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
        exact hy
      have hKy : K (x - y) = ‖x - y‖ ^ (-s) := by
        rw [hK, Set.indicator_of_mem]
        rw [Metric.mem_ball, dist_zero_right]; linarith
      rw [norm_smul, movtr_rieszKernelGrad_norm s hs0 hz, hKy]
      have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
      rw [hyx] at hmv
      have hpow : ‖x - y‖ * ‖x - y‖ ^ (-s - 1) = ‖x - y‖ ^ (-s) := by
        have e := Real.rpow_add hzpos 1 (-s - 1)
        rw [Real.rpow_one] at e
        rw [← e]
        congr 1; ring
      have hnn : 0 ≤ movtr_sigma s * ‖x - y‖ ^ (-s - 1) :=
        mul_nonneg hσ (Real.rpow_nonneg hzpos.le _)
      calc ‖h y - h x‖ * (movtr_sigma s * ‖x - y‖ ^ (-s - 1))
          ≤ (L * ‖x - y‖) * (movtr_sigma s * ‖x - y‖ ^ (-s - 1)) :=
            mul_le_mul_of_nonneg_right hmv hnn
        _ = movtr_sigma s * L * (‖x - y‖ * ‖x - y‖ ^ (-s - 1)) := by ring
        _ = movtr_sigma s * L * ‖x - y‖ ^ (-s) := by rw [hpow]
  · have hnear : s67bd_near d s h x y = 0 := by simp only [s67bd_near, hy, ↓reduceIte]
    rw [hnear, norm_zero]
    exact mul_nonneg (mul_nonneg hσ hL0) (hKnn _)

end HRS.MS.BreakdownS67
