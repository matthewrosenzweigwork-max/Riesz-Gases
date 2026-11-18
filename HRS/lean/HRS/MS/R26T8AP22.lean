import HRS.MS.R26T8AP22l

/-!
# S8.2 local Newton layer, packet T8A.P22: actual Newton integral of the leading harmonic inverse
`r26t8a_leading_newton_commutator_unif`: the T8A.P22 contract with `∃ C` before `B` (so the jet bound `C ‖B‖` is meaningful);
`r26t8a_leading_newton_commutator`: the Pro statement verbatim (constant after `B`), a corollary.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

theorem r26t8a_leading_newton_commutator_unif (d : ℕ) (hd : 2 ≤ d) (nu : ℝ)
    (hnu : 0 < nu) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), (∀ x y, B x y = B y x) →
      ∃ S : Euc d → ℝ, ContDiffOn ℝ ∞ S (Metric.ball 0 1) ∧
        (∀ j ≤ 2, ∀ z ∈ Metric.ball (0 : Euc d) 1, ‖iteratedFDeriv ℝ j S z‖ ≤ C * ‖B‖) ∧
        ∀ z, z ≠ 0 → ‖z‖ < 1 →
          (∫ w, newtonKernel d nu (z - w) * chi w *
            (-(criticalS d / 2) * ‖w‖ ^ (-criticalS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w))) =
            HRS.MS.S82N.s82n_leadingInverse nu B z + S z := by
  obtain ⟨C0, hC00, hC0⟩ := r26t8a_p22_S0_jets hd nu hchi 0
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_p22_S0_jets hd nu hchi 1
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_p22_S0_jets hd nu hchi 2
  refine ⟨C0 + C1 + C2, by positivity, fun B hB => ⟨r26t8a_p22_S0 nu chi B,
    (r26t8a_p22_S0_contDiff hd nu hchi B).contDiffOn, fun j hj z hz => ?_, fun z hz hz1 => ?_⟩⟩
  · have hz' : z ∈ closedBall (0 : Euc d) 1 := ball_subset_closedBall hz
    have hnB : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
    interval_cases j
    · exact (hC0 B z hz').trans (by nlinarith)
    · exact (hC1 B z hz').trans (by nlinarith)
    · exact (hC2 B z hz').trans (by nlinarith)
  · have hcint := r26t8a_p22_Kint hd nu (r26t8a_p22_cfun_contDiff nu B hchi).continuous
      (r26t8a_p22_cfun_cs nu B hchi) z
    have h := r26t8a_p22_identity hd nu hnu hchi B hB hz hz1 hcint
    show _ = _ + 2 * nu * ∫ w, newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w
    exact h

theorem r26t8a_leading_newton_commutator (d : ℕ) (hd : 2 ≤ d) (nu : ℝ)
    (hnu : 0 < nu) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi)
    (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) :
    ∃ S : Euc d → ℝ, ContDiffOn ℝ ∞ S (Metric.ball 0 1) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ 2, ∀ z ∈ Metric.ball (0 : Euc d) 1,
        ‖iteratedFDeriv ℝ j S z‖ ≤ C * ‖B‖) ∧
      ∀ z, z ≠ 0 → ‖z‖ < 1 →
        (∫ w, newtonKernel d nu (z - w) * chi w *
          (-(criticalS d / 2) * ‖w‖ ^ (-criticalS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w))) =
          HRS.MS.S82N.s82n_leadingInverse nu B z + S z := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_leading_newton_commutator_unif d hd nu hnu chi hchi
  obtain ⟨S, hS1, hS2, hS3⟩ := hC B hB
  exact ⟨S, hS1, ⟨C, hC0, hS2⟩, hS3⟩

end HRS.MS.R26T8A
