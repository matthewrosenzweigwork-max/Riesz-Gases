import HRS.MS.SA16E1Liou5

/-!
# S.A.16 E1: helper facts for the geometry assembly
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff BoundedContinuousFunction

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS.Whole.AppendixALemmas

/-- Continuity in time of the columns of the derivative of the flow. -/
theorem e1_col_cont {d m : ℕ} {T Λg : ℝ} {bt : ℝ → Euc d → Euc d} (hT : 0 ≤ T)
    (hb : IsDriftBounds T m Λg bt) {Ψ : ℝ → Euc d → Euc d}
    (hΨ : HRS.Whole.AppendixALemmas.IsNegDriftFlow T bt Ψ) (x v : Euc d) :
    ContinuousOn (fun τ => fderiv ℝ (Ψ τ) x v) (Icc (0:ℝ) T) := by
  obtain ⟨Ξ, hΞ, -, hΞΨ⟩ := HRS.MS.FlowC.fc_exists_param (E := Euc d) hT
    (HRS.MS.FlowB.db_of_drift hb) hΨ.init (fun y => hΨ.eqn y)
  have hΞd : DifferentiableAt ℝ Ξ x :=
    (hΞ.differentiable (by exact_mod_cast Nat.succ_ne_zero m)) x
  have key : ∀ τ ∈ Icc (0:ℝ) T, fderiv ℝ (Ψ τ) x v = (fderiv ℝ Ξ x v) τ := by
    intro τ hτ
    have hfun : Ψ τ = (BoundedContinuousFunction.evalCLM (β := Euc d) ℝ τ) ∘ Ξ :=
      funext fun y => (hΞΨ y τ hτ).symm
    rw [hfun, fderiv_comp x (ContinuousLinearMap.differentiableAt _) hΞd]
    simp
  exact (fderiv ℝ Ξ x v).continuous.continuousOn.congr key

theorem e1_ifd_add_const {d : ℕ} {f : Euc d → Euc d} {n : ℕ} {c : Euc d} (hn : 1 ≤ n)
    (hf : ContDiff ℝ n f) (x : Euc d) :
    iteratedFDeriv ℝ n (fun y => f y + c) x = iteratedFDeriv ℝ n f x := by
  have hc : ContDiffAt ℝ n (fun _ : Euc d => c) x := contDiffAt_const
  have e : (fun y => f y + c) = f + fun _ => c := rfl
  rw [e, iteratedFDeriv_add_apply hf.contDiffAt hc,
    iteratedFDeriv_const_of_ne (Nat.one_le_iff_ne_zero.1 hn)]
  simp

end HRS.Whole.AppendixA.Phase2SA16Evolution
