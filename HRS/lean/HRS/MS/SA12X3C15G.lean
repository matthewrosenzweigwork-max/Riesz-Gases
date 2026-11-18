import HRS.MS.SA12X3C15F

/-!
# S.A.12 C15 (SA12X3), part G: continuity in time of a parametric integral with uniformly bounded support
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_param_cont {t R : ℝ} (ht : 0 ≤ t) {h : ℝ → Euc d → ℝ}
    (hc : ContinuousOn (fun p : ℝ × Euc d => h p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ))
    (hs : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, R < ‖x‖ → h τ x = 0) :
    ContinuousOn (fun τ => ∫ x, h τ x) (Icc (0 : ℝ) t) := by
  set H : ℝ → Euc d → ℝ := fun τ x => h (Set.projIcc (0 : ℝ) t ht τ : ℝ) x with hH
  have hcomp : Continuous (fun p : ℝ × Euc d => ((Set.projIcc (0 : ℝ) t ht p.1 : ℝ), p.2)) :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
  have hHc : Continuous (Function.uncurry H) := by
    have := hc.comp_continuous hcomp (fun p => ⟨(Set.projIcc (0 : ℝ) t ht p.1).2, mem_univ _⟩)
    exact this
  have hint := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Euc d))) hHc
    (isCompact_closedBall (0 : Euc d) R)
  refine hint.continuousOn.congr fun τ hτ => ?_
  show ∫ x, h τ x = ∫ x in closedBall (0 : Euc d) R, h (Set.projIcc (0 : ℝ) t ht τ : ℝ) x
  rw [Set.projIcc_of_mem ht hτ]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro x hx
  exact hs τ hτ x (by simpa [mem_closedBall_zero_iff, not_le] using hx)

end HRS.MH.AdjointRd.Phase2SA12Construction
