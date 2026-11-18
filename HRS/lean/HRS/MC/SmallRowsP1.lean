import HRS.Energy.Modulated
import HRS.Torus.Sobolev
import HRS.Prob.Gaussian
import HRS.MC.L5566

/-!
# Packet SM1: the force of the negative-spectral kernel is not Lipschitz (`M:@remark:L5566`, clause R1)

Proves `negSpectral_force_not_lipschitz` (statement frozen in `HRS/MC/SmallRowsSpec.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option maxSynthPendingDepth 3

namespace HRS.MC.SmallRows

open HRS

/-- The canonical representative of a torus point lies in the box `[0,1)^d`, hence has norm at
most `√d`. -/
theorem p_sm1_rep_norm_le {d : ℕ} (x : Torus d) : ‖Torus.rep x‖ ≤ Real.sqrt d := by
  have hcoord : ∀ i : Fin d, ‖Torus.rep x i‖ ≤ 1 := by
    intro i
    have h := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    have h' : 0 ≤ Torus.rep x i ∧ Torus.rep x i < 1 := by
      simpa [Torus.rep] using h
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h'.1, h'.2]
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i : Fin d, ‖Torus.rep x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h0 : 0 ≤ ‖Torus.rep x i‖ := norm_nonneg _
        nlinarith [hcoord i]
    _ = d := by simp

/-! ### Row `M:@remark:L5566`, clause R1 -/

theorem negSpectral_force_not_lipschitz {d : ℕ} (hd : 1 ≤ d) {s c : ℝ} (hs1 : -1 < s)
    (hs0 : s < 0) (hc : 0 < c) :
    (∃ M : ℝ, ∀ x : Torus d, |negSpectralKernel d s c x| ≤ M) ∧
    ¬ ∃ K : ℝ≥0, LipschitzWith K
        (fun y : Euc d => Torus.grad (negSpectralKernel d s c) (Torus.mk y)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
      (negSpectralKernel_continuous d hs0 hc).continuousOn
    exact ⟨M, fun x => by rw [← Real.norm_eq_abs]; exact hM x (Set.mem_univ x)⟩
  · rintro ⟨K, hK⟩
    obtain ⟨x, -, -, hx⟩ := HRS.MC.L5566.negSpectral_grad_unbounded_proof hd hs1 hs0 hc
      (‖Torus.grad (negSpectralKernel d s c) (Torus.mk 0)‖ + (K : ℝ) * Real.sqrt d)
    have hlip := hK.dist_le_mul (Torus.rep x) 0
    simp only [Torus.mk_rep, dist_eq_norm, sub_zero] at hlip
    have h1 : ‖Torus.grad (negSpectralKernel d s c) x - Torus.grad (negSpectralKernel d s c) (Torus.mk 0)‖
        ≤ (K : ℝ) * Real.sqrt d :=
      hlip.trans (mul_le_mul_of_nonneg_left (p_sm1_rep_norm_le x) (NNReal.coe_nonneg K))
    have h2 : ‖Torus.grad (negSpectralKernel d s c) x‖
        ≤ ‖Torus.grad (negSpectralKernel d s c) x - Torus.grad (negSpectralKernel d s c) (Torus.mk 0)‖
          + ‖Torus.grad (negSpectralKernel d s c) (Torus.mk 0)‖ := by
      calc ‖Torus.grad (negSpectralKernel d s c) x‖
          = ‖(Torus.grad (negSpectralKernel d s c) x - Torus.grad (negSpectralKernel d s c) (Torus.mk 0))
              + Torus.grad (negSpectralKernel d s c) (Torus.mk 0)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith

end HRS.MC.SmallRows
