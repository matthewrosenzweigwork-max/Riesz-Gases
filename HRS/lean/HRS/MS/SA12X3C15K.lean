import HRS.MS.SA12X3C15J
import HRS.MS.SA12X3C7D3

/-!
# S.A.12 C15 (SA12X3), part K: small algebraic facts (linearity of `lambdaM` in `C`, `jetPair` against `-N + 0`)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_lam_lin {Rg : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν ν₀ : ℝ}
    (hR : RdRegimeHolds Rg d s M ν ν₀) (θ : ℝ) :
    ∃ k : ℝ, 1 ≤ k ∧ ∀ C : ℝ, Rg.lambdaM C ν₀ θ = C * k := by
  cases Rg with
  | R3 =>
    have hu : 0 ≤ ν₀ ^ (-(θ / (2 - θ))) := Real.rpow_nonneg hR.2.1.le _
    exact ⟨1 + ν₀ ^ (-(θ / (2 - θ))), by linarith, fun C => rfl⟩
  | R2b _ => exact absurd hR id
  | R1 => exact ⟨1, le_rfl, fun C => by simp [PDE.Regime.lambdaM]⟩
  | R2a => exact ⟨1, le_rfl, fun C => by simp [PDE.Regime.lambdaM]⟩
  | R2c => exact ⟨1, le_rfl, fun C => by simp [PDE.Regime.lambdaM]⟩

theorem sa12x3_pd_neg_add_zero {n : ℕ} (idx : Fin n → Fin d) (N : Euc d → ℝ) (x : Euc d) :
    partialDeriv idx (fun y => -N y + 0) x = -partialDeriv idx N x := by
  unfold partialDeriv
  have : (fun y => -N y + 0) = -N := by funext y; simp
  rw [this, iteratedFDeriv_neg_apply]
  simp

theorem sa12x3_jetPair_neg (m : ℕ) (w F N : Euc d → ℝ) :
    jetPair m w F (fun y => -N y + 0) = -jetPair m w F N := by
  unfold jetPair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [← integral_neg]
  congr 1
  funext x
  rw [sa12x3_pd_neg_add_zero]; ring

end HRS.MH.AdjointRd.Phase2SA12Construction
