import HRS.MC.L2C5Aux1

/-!
# Packet L2C-5, helper 2: continuity of the cross gradient energies of two classical solutions

For classical adjoint solutions `F`, `G` on `[0,t]` (possibly for different densities) and a weight `w(r,x)`
continuous on `[0,t] × 𝕋^d`, the maps
`r ↦ ∫ ⟨∇F r, ∇G r⟩ w(r,·)` and `r ↦ ∫ w ‖∇F r - ∇G r‖²` are continuous on `[0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFLinear

namespace HRS.MC.L2C5

variable {d : ℕ}

theorem l2c5_grad_prod_cont {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => Torus.grad (F p.1) p.2 := by
  have : (fun p : Set.Icc (0 : ℝ) t × Torus d => Torus.grad (F p.1) p.2) =
      fun p => WithLp.toLp 2 (fun i => Torus.partialDeriv i (F p.1) p.2) := by
    funext p; ext i; simp [MFAux.grad_apply]
  rw [this]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_partialDeriv_prod hF i)

theorem l2c5_cross_cont {D D' : DynData d} {μ μ' : ℝ → Torus d → ℝ} {t : ℝ} {φ φ' : Torus d → ℝ}
    {F G : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F)
    (hG : IsClassicalAdjointSolution D' μ' t φ' G) {w : ℝ → Torus d → ℝ}
    (hw : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => w p.1 p.2) :
    ContinuousOn (fun r => ∫ x, inner ℝ (Torus.grad (F r) x) (Torus.grad (G r) x) * w r x)
      (Set.Icc 0 t) := by
  refine l2c5_cont_param ?_
  exact (l2c5_grad_prod_cont hF).inner (l2c5_grad_prod_cont hG) |>.mul hw

theorem l2c5_diff_cont {D D' : DynData d} {μ μ' : ℝ → Torus d → ℝ} {t : ℝ} {φ φ' : Torus d → ℝ}
    {F G : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F)
    (hG : IsClassicalAdjointSolution D' μ' t φ' G) {w : Torus d → ℝ} (hw : Continuous w) :
    ContinuousOn (fun r => ∫ x, w x * ‖Torus.grad (F r) x - Torus.grad (G r) x‖ ^ 2) (Set.Icc 0 t) := by
  refine l2c5_cont_param ?_
  exact (hw.comp continuous_snd).mul
    (((l2c5_grad_prod_cont hF).sub (l2c5_grad_prod_cont hG)).norm.pow 2)

end HRS.MC.L2C5
