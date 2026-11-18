import HRS.Whole.AppendixA

/-!
# S.A.12 B8: monotonicity of the rate `Λ_m` in the constant
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

-- BEGIN SA12.B8
theorem rate_mono (Rg : PDE.Regime) (C C' ν₀ s ν : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hR : RdRegimeHolds Rg d s M ν ν₀)
    (hC : 0≤C) (hCC : C≤C') :
    0≤Rg.lambdaM C ν₀ (PDE.thetaOrder d s) ∧
      Rg.lambdaM C ν₀ (PDE.thetaOrder d s) ≤ Rg.lambdaM C' ν₀ (PDE.thetaOrder d s) := by
  cases Rg with
  | R3 =>
    obtain ⟨-, hν₀, -⟩ := hR
    have hp : 0 ≤ 1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s))) := by
      have := Real.rpow_nonneg hν₀.le (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))
      linarith
    simp only [PDE.Regime.lambdaM]
    exact ⟨mul_nonneg hC hp, mul_le_mul_of_nonneg_right hCC hp⟩
  | R2b _ => exact absurd hR (by simp [RdRegimeHolds])
  | R1 => exact ⟨by simpa [PDE.Regime.lambdaM] using hC, by simpa [PDE.Regime.lambdaM] using hCC⟩
  | R2a => exact ⟨by simpa [PDE.Regime.lambdaM] using hC, by simpa [PDE.Regime.lambdaM] using hCC⟩
  | R2c => exact ⟨by simpa [PDE.Regime.lambdaM] using hC, by simpa [PDE.Regime.lambdaM] using hCC⟩
-- END SA12.B8

end HRS.MH.AdjointRd.Phase2SA12Companions
