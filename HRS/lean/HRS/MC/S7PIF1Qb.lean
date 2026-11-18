import HRS.MC.S7PIF1Qa
import HRS.MC.S7PIDefs
import HRS.MC.S7PIDEMain
import HRS.Equilibrium.LocalDivMain
import HRS.Equilibrium.LocalDivTorus
import HRS.Equilibrium.FieldSingAux
import HRS.Kernel.GradReg
import HRS.Kernel.GradOp
import HRS.PDE.Convention
import HRS.Stochastic.Duality

/-!
# Packet piF1 (F2), part b: the transport kernels `h_{e_k}` and the expansion of `h_ψ`

For `ψ` smooth with real Fourier coefficients `a_k` and `G = ∇g = periodicRieszGrad d s`:
* `|h_{e_k}(x,y)| ≤ c₁ ⟨k⟩ ‖G(x - y)‖` (`S7PIF1_hT_mode_bound`), `c₁ = 2√2 d`;
* `h_ψ(x,y) = ∑_k a_k h_{e_k}(x,y)` for all `x,y` (`S7PIF1_hT_hasSum`), from the gradient series
  `S7PIDE_grad_series`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS

variable {d : ℕ}

/-- The bound `|h_{e_k}(x,y)| ≤ 2√2 d ⟨k⟩ ‖G(x - y)‖`. -/
theorem S7PIF1_hT_mode_bound (s : ℝ) (k : NonzeroLattice d) (x y : Torus d) :
    |hTransport d s (Torus.realMode k) x y|
      ≤ (2 * Real.sqrt 2 * d) * Lattice.jp k.1 * ‖periodicRieszGrad d s (x - y)‖ := by
  rw [HRS.LocalDivAux.hTransport_eq s _ (HRS.FieldSingAux.isSmooth_realMode k)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hi : ∀ i : Fin d, |(Torus.partialDeriv i (Torus.realMode k) x - Torus.partialDeriv i (Torus.realMode k) y) *
        (periodicRieszGrad d s (x - y)) i|
      ≤ (2 * Real.sqrt 2 * Lattice.jp k.1) * ‖periodicRieszGrad d s (x - y)‖ := by
    intro i
    rw [abs_mul]
    have h1 : |Torus.partialDeriv i (Torus.realMode k) x| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
      rw [← S7PIDE.S7PIDE_grad_apply]; exact S7PIDE.S7PIDE_grad_comp_le k x i
    have h2 : |Torus.partialDeriv i (Torus.realMode k) y| ≤ Real.sqrt 2 * Lattice.jp k.1 := by
      rw [← S7PIDE.S7PIDE_grad_apply]; exact S7PIDE.S7PIDE_grad_comp_le k y i
    have h3 : |(periodicRieszGrad d s (x - y)) i| ≤ ‖periodicRieszGrad d s (x - y)‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le _ i
    have habs : |Torus.partialDeriv i (Torus.realMode k) x - Torus.partialDeriv i (Torus.realMode k) y|
        ≤ 2 * Real.sqrt 2 * Lattice.jp k.1 := (abs_sub _ _).trans (by linarith)
    have hj := Torus.jp_pos k.1
    exact mul_le_mul habs h3 (abs_nonneg _) (by positivity)
  calc _ ≤ ∑ _i : Fin d, (2 * Real.sqrt 2 * Lattice.jp k.1) * ‖periodicRieszGrad d s (x - y)‖ :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp; ring

/-- `h_ψ = ∑_k a_k h_{e_k}` pointwise, for smooth `ψ`. -/
theorem S7PIF1_hT_hasSum (s : ℝ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (x y : Torus d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff ψ k * hTransport d s (Torus.realMode k) x y)
      (hTransport d s ψ x y) := by
  have hU : MemSobolev ((d + 3 : ℕ) : ℝ) ψ := PDE.MFSemigroup.memSobolev_of_isSmooth hψ _
  have hc : Continuous ψ := by
    have : Torus.IsCk 1 ψ := ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from hψ)
      (by exact_mod_cast le_top)
    exact HRS.KernelGrad.isCk_continuous this
  have h1 : Torus.IsCk 1 ψ := ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from hψ)
      (by exact_mod_cast le_top)
  have hn : (d : ℝ) / 2 + 2 < ((d + 3 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hser := fun (z : Torus d) (i : Fin d) => S7PIDE.S7PIDE_grad_series hn hU hc h1 z i
  rw [HRS.LocalDivAux.hTransport_eq s ψ hψ]
  have : ∀ k : NonzeroLattice d, Torus.funRealCoeff ψ k * hTransport d s (Torus.realMode k) x y
      = ∑ i, (Torus.funRealCoeff ψ k * Torus.grad (Torus.realMode k) x i
          - Torus.funRealCoeff ψ k * Torus.grad (Torus.realMode k) y i) * (periodicRieszGrad d s (x - y)) i := by
    intro k
    rw [HRS.LocalDivAux.hTransport_eq s _ (HRS.FieldSingAux.isSmooth_realMode k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← S7PIDE.S7PIDE_grad_apply, ← S7PIDE.S7PIDE_grad_apply]
    ring
  simp_rw [this]
  refine hasSum_sum fun i _ => ?_
  have hx := hser x i
  have hy := hser y i
  simp_rw [S7PIDE.S7PIDE_grad_apply] at hx hy ⊢
  exact ((hx.sub hy).mul_right _)

end HRS.MC.Sec7.S7PIF1

end
