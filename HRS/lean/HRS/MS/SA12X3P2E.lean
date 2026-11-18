import HRS.MS.SA12X3P2D
import HRS.MS.SA12V3U
import HRS.MS.SA12K15
import HRS.MS.Ker1Aux2

/-!
# S.A.12 P2 (SA12X3), part E: the cutoff `ζ`, the mollifier `η` and the periodic Riesz kernels
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3p_zeta : ∃ ζ : Euc d → ℝ, IsCutoffRad (1 / 4) (1 / 3) ζ := by
  let f : ContDiffBump (0 : Euc d) := ⟨1 / 4, 3 / 10, by norm_num, by norm_num⟩
  refine ⟨⇑f, f.contDiff, f.hasCompactSupport, ?_, fun x => ⟨f.nonneg, f.le_one⟩, fun x hx => ?_⟩
  · rw [f.tsupport_eq]
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    have : ‖x‖ ≤ 3 / 10 := hx
    linarith
  · exact f.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff] at hx ⊢; show ‖x‖ ≤ 1 / 4; simpa using hx)

theorem sa12x3p_eta : ∃ η : Euc d → ℝ, IsMollifier η := by
  let f : ContDiffBump (0 : Euc d) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_, fun x => f.nonneg_normed x,
    f.integral_normed⟩
  rw [f.tsupport_normed_eq]

theorem sa12x3p_gamma (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ γ : ℝ → Euc d → ℝ, ∀ L : ℝ, 1 ≤ L → IsPeriodicRieszKernel d s L (γ L) :=
  ⟨fun L => HRS.MS.Ker1.ker1_gam d s L, fun L hL =>
    HRS.MS.Ker1.ker1_gam_isKernel hd hs0 hsd (by linarith)⟩

end HRS.MH.AdjointRd.Phase2SA12Assembly
