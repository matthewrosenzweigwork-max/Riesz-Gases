import HRS.MS.SA12X3C9D

/-!
# S.A.12 C9 (SA12X3), part E: the local energy rate of one jet
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MS.UniqT3
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_inner_grad_fd (b : Euc d) (w : Euc d → ℝ) (x : Euc d) :
    inner ℝ b (gradient w x) = fderiv ℝ w x b := by
  rw [real_inner_comm, HRS.MS.Wad.s83_inner_gradient]

theorem sa12x3_rate_decomp {m n : ℕ} (hn : n ≤ m) {b : Euc d → Euc d} (hbC : ContDiff ℝ (m + 1) b)
    {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (ν : ℝ) (idx : Fin n → Fin d) {w : Euc d → ℝ}
    (x : Euc d) :
    2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) +
      2 * w x * inner ℝ (b x) (gradient w x) * partialDeriv idx F x ^ 2 =
    ν * (2 * w x ^ 2 * partialDeriv idx F x * ∑ i : Fin d, D1 i (D1 i (partialDeriv idx F)) x) +
      (2 * w x ^ 2 * (partialDeriv idx F x * fderiv ℝ (partialDeriv idx F) x (b x)) +
        2 * w x * fderiv ℝ w x (b x) * partialDeriv idx F x ^ 2) +
      2 * w x ^ 2 * (partialDeriv idx F x * (partialDeriv idx (fun y => inner ℝ (b y) (gradient F y)) x -
        fderiv ℝ (partialDeriv idx F) x (b x))) +
      2 * w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x) := by
  rw [sa12x3_pd_rate hn hbC hF hG ν idx x, sa12x3_inner_grad_fd]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
