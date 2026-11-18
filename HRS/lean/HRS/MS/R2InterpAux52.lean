import HRS.MS.R2InterpAux51

/-!
# S10.2 (worker S102), part 52 (packet F6, regularity): continuity in the starting time of the Gram integrals of the grid orbits

For classical adjoint solutions `f` (`IsClassicalAdjointW`) the gradient `∇f_r(x)` is continuous in `r ∈ [0,t]` and bounded; hence the Gram integral
`v ↦ ∫ ∇U^{v,t_k}φ·∇U^{v,t_{k'}}φ' ρ dx` is continuous on `[0, t_k ∧ t_{k'}]` for an integrable (stationary) density.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.S7PIL

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

theorem s102_propagator_classical {t : ℝ} {φ : Euc d → ℝ} (h : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = h.choose := by
    funext r
    unfold propagatorW
    rw [dif_pos h]
  rw [this]
  exact h.choose_spec

theorem s102_grad_contOn {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (x : Euc d) (a : Fin d) : ContinuousOn (fun r => gradient (f r) x a) (Icc 0 t) := by
  have hc := hf.cont_c2 1 (by norm_num)
  have h1 : Continuous fun r : Icc (0 : ℝ) t => gradient (f r) x a := by
    have := (S7PIL_ev (fun _ : Fin 1 => (EuclideanSpace.single a (1 : ℝ) : Euc d))).continuous.comp
      (hc.comp (Continuous.prodMk continuous_id continuous_const (Y := Euc d)) :
        Continuous fun r : Icc (0 : ℝ) t => iteratedFDeriv ℝ 1 (f r) x)
    refine this.congr fun r => ?_
    simp [S7PIL_ev_apply, iteratedFDeriv_one_apply, s102_gradient_apply]
  exact continuousOn_iff_continuous_restrict.2 h1

theorem s102_grad_bdd {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ x a, |gradient (f r) x a| ≤ B := by
  obtain ⟨B, hB⟩ := hf.bdd 1 (by norm_num)
  refine ⟨B, fun r hr x a => ?_⟩
  have h1 := (iteratedFDeriv ℝ 1 (f r) x).le_opNorm (fun _ : Fin 1 => (EuclideanSpace.single a (1 : ℝ) : Euc d))
  simp only [iteratedFDeriv_one_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
    EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [s102_gradient_apply, ← Real.norm_eq_abs]
  exact h1.trans (hB r hr x)

end HRS.MS.R2Interp

end
