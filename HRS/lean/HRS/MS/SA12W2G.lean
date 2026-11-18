import HRS.MS.SA12W2F

/-!
# S.A.12 C5 (SA12W2 worker), part G: the unit-torus data and its `AdjointData` at every level (`R26-T5.T01/T02`)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

/-- Weak continuity of the rescaled density path (dominated convergence on the compact torus). -/
theorem sa12w2_dens_cont {L T t : ℝ} (hL : 0 < L) (hT0 : 0 ≤ T) {μ : ℝ → Euc d → ℝ}
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x)
    (hsm : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ)) (hTime : PeriodicTimeSmooth T μ)
    (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    Continuous fun r : ℝ => ∫ x, ψ x * sa12w2_dens L (μ (sa12w2_tau t T r)) x := by
  obtain ⟨B0, B1, hB⟩ := sa12v_mu_bounds L T hL μ hper hTime
  obtain ⟨Bψ, hBψ⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.continuousOn
  have hdens : ∀ r : ℝ, Continuous (sa12w2_dens L (μ (sa12w2_tau t T r))) := fun r =>
    Torus.continuous_of_continuous_lift
      (sa12w2_contDiff_desc (f := fun x => L ^ d * μ (sa12w2_tau t T r) x)
        (fun x z => by rw [hper _ (sa12w2_tau_mem hT0 r) x z]) hL.ne'
        (contDiff_const.mul (((hsm _ (sa12w2_tau_mem hT0 r)).of_le (by simp)))) (n := 0)).continuous
  refine continuous_of_dominated (bound := fun _ => Bψ * (L ^ d * B0)) (fun r => ?_) (fun r => ?_)
    (integrable_const _) (Filter.Eventually.of_forall fun x => ?_)
  · exact (hψ.mul (hdens r)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul]
    have h1 := hBψ x (mem_univ _)
    have h2 : ‖sa12w2_dens L (μ (sa12w2_tau t T r)) x‖ ≤ L ^ d * B0 := by
      show ‖L ^ d * μ (sa12w2_tau t T r) (L • Torus.rep x)‖ ≤ _
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hL.le _)]
      exact mul_le_mul_of_nonneg_left (hB _ (sa12w2_tau_mem hT0 r) _).1 (pow_nonneg hL.le _)
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  · have hj := sa12v_mu_joint T μ hTime
    have hc : Continuous fun r : ℝ => μ (sa12w2_tau t T r) (L • Torus.rep x) := by
      refine hj.comp_continuous (f := fun r : ℝ => (sa12w2_tau t T r, L • Torus.rep x)) ?_
        fun r => ⟨sa12w2_tau_mem hT0 r, mem_univ _⟩
      exact (((continuous_const.sub continuous_id).max continuous_const).min continuous_const).prodMk
        continuous_const
    exact continuous_const.mul (continuous_const.mul hc)

end HRS.PDE.SA12W2
