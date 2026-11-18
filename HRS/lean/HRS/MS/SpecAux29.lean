import HRS.MS.SpecAux19
import HRS.MS.MovLinAux9

/-!
# S8P: the standing hypotheses `S8pRho` hold for the thermal density (S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_rho_of_thermal`: for `Mov2dTh d s β q ρ` with `0 < s` (e.g. the critical
`s = d/2`), `ρ` is a bounded probability density with `∫ρ = 1` (`√ρ` is a Schwartz function), i.e. `S8pRho d s ρ M` for some `M`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

theorem s8p_rho_of_thermal (H : Mov2dTh d s β q ρ) (hs : 0 < s) : ∃ M : ℝ, S8pRho d s ρ M := by
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  obtain ⟨hsm, hpos⟩ := mov2d_rho_data H
  have hprob : HRS.Whole.IsProbDensity ρ := H.hρ.1.1
  have hint : Integrable ρ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hprob.integral_one]; exact one_ne_zero
  refine ⟨‖ψ0.toBoundedContinuousFunction‖ ^ 2, hs, H.hsd, hprob.measurable, hprob.nonneg, fun x => ?_, hint,
    hprob.integral_one⟩
  have h1 : |ψ0 x| ≤ ‖ψ0.toBoundedContinuousFunction‖ := by
    have := ψ0.toBoundedContinuousFunction.norm_coe_le_norm x
    simpa using this
  have h2 : ρ x = ψ0 x ^ 2 := by
    have := congrFun hψ0 x
    rw [show ψ0 x = Real.sqrt (ρ x) from this, Real.sq_sqrt (hprob.nonneg x)]
  rw [h2]
  exact (sq_le_sq.2 (by rwa [abs_of_nonneg (norm_nonneg _)])).trans_eq' rfl |>.trans_eq rfl

end HRS.MS.Spec
