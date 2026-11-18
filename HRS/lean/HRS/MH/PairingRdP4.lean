import HRS.MH.PairingRdDefs
import HRS.MH.ScreenedA7
import HRS.MP.RdGenConv

/-!
# PairingRd packet PR4 (`conv_integrand_bound_rd`): pointwise bound of the cancellation integrand

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: `kernel_bound_proof`
(`HRS/MH/ScreenedA7.lean`, `‖∇g u‖ ≤ max 1 s ‖u‖^(-s-1)`) and `rg_pow_far` (`HRS/MP/RdGenConv.lean`) for the
far field; the near field uses `rpow_add`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR4** `conv_integrand_bound_rd` (proof). -/
theorem conv_integrand_bound_rd {s : ℝ} (hs0 : 0 ≤ s) {h : Euc d → ℝ} {Λ β : ℝ} (hΛ : 0 ≤ Λ)
    (hH : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x y : Euc d) (hxy : x ≠ y) :
    ‖convInt (Whole.rieszKernelGrad d s) h x y‖ ≤
      max 1 s * (Λ * Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun z => ‖z‖ ^ (β - s - 1)) (x - y)
        + 4 ^ (s + 1) * |h y|) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
  have hG : ‖Whole.rieszKernelGrad d s (x - y)‖ ≤ max 1 s * ‖x - y‖ ^ (-s - 1) :=
    HRS.MH.Screened.kernel_bound_proof hs0 (x - y) hz
  have hσ : 0 ≤ max 1 s := (zero_le_one).trans (le_max_left _ _)
  have hh0 : 0 ≤ |h y| := abs_nonneg _
  unfold convInt
  split_ifs with hc
  · -- near field: `|h y - h x| ≤ Λ ‖x - y‖^β` and `‖∇g‖ ≤ σ ‖x - y‖^(-s-1)`
    have hH' := hH x (x - y) hc
    rw [sub_sub_cancel] at hH'
    have hind : Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun z => ‖z‖ ^ (β - s - 1)) (x - y)
        = ‖x - y‖ ^ (β - s - 1) := Set.indicator_of_mem (by simpa using hc) _
    rw [hind, norm_smul, Real.norm_eq_abs]
    have hmul : |h y - h x| * ‖Whole.rieszKernelGrad d s (x - y)‖
        ≤ (Λ * ‖x - y‖ ^ β) * (max 1 s * ‖x - y‖ ^ (-s - 1)) :=
      mul_le_mul hH' hG (norm_nonneg _) (mul_nonneg hΛ (Real.rpow_nonneg (norm_nonneg _) _))
    have hpr : ‖x - y‖ ^ β * ‖x - y‖ ^ (-s - 1) = ‖x - y‖ ^ (β - s - 1) := by
      rw [← Real.rpow_add hzpos]; congr 1; ring
    have hEq : (Λ * ‖x - y‖ ^ β) * (max 1 s * ‖x - y‖ ^ (-s - 1))
        = max 1 s * (Λ * ‖x - y‖ ^ (β - s - 1)) := by
      rw [← hpr]; ring
    have h4 : 0 ≤ max 1 s * (4 ^ (s + 1) * |h y|) :=
      mul_nonneg hσ (mul_nonneg (by positivity) hh0)
    calc _ ≤ _ := hmul
      _ = max 1 s * (Λ * ‖x - y‖ ^ (β - s - 1)) := hEq
      _ ≤ max 1 s * (Λ * ‖x - y‖ ^ (β - s - 1) + 4 ^ (s + 1) * |h y|) := by
          rw [mul_add]; exact le_add_of_nonneg_right h4
  · -- far field: the indicator vanishes and `‖∇g‖ ≤ σ 4^(s+1)`
    have hc' : 1 / 4 < ‖x - y‖ := not_le.mp hc
    have hind : Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (fun z => ‖z‖ ^ (β - s - 1)) (x - y)
        = 0 := Set.indicator_of_notMem (by simpa using hc) _
    have hfar : ‖x - y‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := HRS.MP.RdGen.rg_pow_far hs0 hc'
    have hG2 : ‖Whole.rieszKernelGrad d s (x - y)‖ ≤ max 1 s * 4 ^ (s + 1) :=
      hG.trans (mul_le_mul_of_nonneg_left hfar hσ)
    rw [hind, mul_zero, zero_add, norm_smul, Real.norm_eq_abs]
    refine (mul_le_mul_of_nonneg_left hG2 hh0).trans (le_of_eq ?_)
    ring

end HRS.MH.PairingRdP
