import HRS.MS.SA12X3N1D
import HRS.MS.SA12BuildC18

/-!
# S.A.12 N1/N2 (SA12X3), part E: near regime of the periodic kernel convolved with a mean-zero test function
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_conv_near (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ : ℝ) (q : Euc d → ℝ), 0 < δ ∧ ContDiff ℝ ∞ q ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ,
      IsPeriodicRieszKernel d s L γ → ∀ (R : ℝ) (Q : Euc d → ℝ), Continuous Q → tsupport Q ⊆ closedBall 0 R →
        ∫ u, Q u = 0 → ∀ x : Euc d, ‖x‖ + R < δ * L →
          HRS.Whole.convFun γ Q x = HRS.Whole.convFun (rieszKernel d s) Q x +
            L ^ (-s) * ∫ w, q (L⁻¹ • w) * Q (x - w) := by
  obtain ⟨δ, q, hδ, hq, hloc⟩ := periodic_kernel_local hd s hs0 hsd
  refine ⟨δ, q, hδ, hq, fun L hL γ hγ R Q hQ hQs hQ0 x hx => ?_⟩
  obtain ⟨c, -, hid⟩ := hloc L hL γ hγ
  have hQcs : HasCompactSupport Q :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
      ((subset_tsupport Q).trans hQs)
  have hcs' : HasCompactSupport (fun w => Q (x - w)) := hQcs.comp_homeomorph (Homeomorph.subLeft x)
  have hc' : Continuous (fun w => Q (x - w)) := hQ.comp (continuous_const.sub continuous_id)
  have hconv : ∀ K : Euc d → ℝ, HRS.Whole.convFun K Q x = ∫ w, K w * Q (x - w) := by
    intro K
    have h := integral_sub_left_eq_self (μ := volume) (fun t => K t * Q (x - t)) x
    simp only [sub_sub_cancel] at h
    unfold HRS.Whole.convFun
    rw [← h]
  have hint0 : ∫ w, Q (x - w) = 0 := by
    have h := integral_sub_left_eq_self (μ := volume) Q x
    rw [h, hQ0]
  have hg : Integrable (fun w => rieszKernel d s w * Q (x - w)) volume :=
    (rieszKernel_locallyIntegrable hs0 hsd).integrable_smul_right_of_hasCompactSupport hc' hcs'
  have hQi : Integrable (fun w => Q (x - w)) volume := hc'.integrable_of_hasCompactSupport hcs'
  have hqc : Continuous (fun w : Euc d => q (L⁻¹ • w) * Q (x - w)) :=
    (hq.continuous.comp (continuous_const_smul L⁻¹)).mul hc'
  have hqcs : HasCompactSupport (fun w : Euc d => q (L⁻¹ • w) * Q (x - w)) := hcs'.mul_left
  have hqi : Integrable (fun w : Euc d => q (L⁻¹ • w) * Q (x - w)) volume :=
    hqc.integrable_of_hasCompactSupport hqcs
  rw [hconv γ, hconv (rieszKernel d s)]
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hae : ∀ᵐ w ∂(volume : Measure (Euc d)), γ w * Q (x - w) =
      rieszKernel d s w * Q (x - w) + c * Q (x - w) + L ^ (-s) * (q (L⁻¹ • w) * Q (x - w)) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))] with w hw0
    by_cases hQw : Q (x - w) = 0
    · rw [hQw]; simp
    · have hmem := hQs (subset_tsupport Q hQw)
      rw [mem_closedBall, dist_zero_right] at hmem
      have hwn : ‖w‖ < δ * L := by
        have : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
          calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        linarith
      rw [hid w hw0 hwn]; ring
  have e1 : ∫ w, (rieszKernel d s w * Q (x - w) + c * Q (x - w) + L ^ (-s) * (q (L⁻¹ • w) * Q (x - w))) =
      (∫ w, (rieszKernel d s w * Q (x - w) + c * Q (x - w))) + ∫ w, L ^ (-s) * (q (L⁻¹ • w) * Q (x - w)) :=
    integral_add (f := fun w => rieszKernel d s w * Q (x - w) + c * Q (x - w))
      (g := fun w => L ^ (-s) * (q (L⁻¹ • w) * Q (x - w))) (hg.add (hQi.const_mul c)) (hqi.const_mul _)
  have e2 : ∫ w, (rieszKernel d s w * Q (x - w) + c * Q (x - w)) =
      (∫ w, rieszKernel d s w * Q (x - w)) + ∫ w, c * Q (x - w) :=
    integral_add (f := fun w => rieszKernel d s w * Q (x - w)) (g := fun w => c * Q (x - w)) hg (hQi.const_mul c)
  rw [integral_congr_ae hae, e1, e2, integral_const_mul, integral_const_mul, hint0]
  ring

end HRS.MH.AdjointRd.Phase2SA12Construction
