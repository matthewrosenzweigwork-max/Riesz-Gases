import HRS.MS.SA12X3W5B

/-!
# S.A.12 C5-T06 (SA12X3), part C: the periodic nonlocal term of a smooth torus path is again a smooth torus path
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x3w_nonlocal_JC (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L T t : ℝ} (hL : 0 < L) (ht : t ≤ T)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (M : Matrix (Fin d) (Fin d) ℝ) {μ : ℝ → Euc d → ℝ}
    (hTime : PeriodicTimeSmooth T μ) (hsm : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ))
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x)
    {u : ℝ → Torus d → ℝ} (hu : sa12w2_JC t u) :
    ∃ n : ℝ → Torus d → ℝ, sa12w2_JC t n ∧ ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d,
      perNonlocal L γ M (μ τ) (fun x => Torus.lift (u τ) (L⁻¹ • x)) x = Torus.lift (n τ) (L⁻¹ • x) := by
  set M₁ : Matrix (Fin d) (Fin d) ℝ := (L ^ (-s - 2)) • M with hM₁
  have hCCu : sa12w2_CC t u := sa12w2_JC_to_CC hu
  have hdens : sa12w2_CC t (fun τ => sa12w2_dens L (μ τ)) := sa12w2_JC_to_CC (sa12x3w_dens_JC hL ht hTime hsm hper)
  have hgrad : ∀ k : Fin d, sa12w2_CC t (fun τ y => Torus.grad (u τ) y k) := by
    intro k
    have e : (fun τ y => Torus.grad (u τ) y k) =
        fun τ => HRS.KernelGrad.dirTor (u τ) (EuclideanSpace.single k (1 : ℝ)) :=
      funext fun τ => sa12x3w_grad_eq_dir (u τ) k
    rw [e]
    exact sa12w2_CC_dir hCCu _ (by simp)
  have hmv : ∀ i : Fin d, sa12w2_CC t (fun τ y => Torus.matVec M₁.transpose (Torus.grad (u τ) y) i) := by
    intro i
    have e : (fun τ y => Torus.matVec M₁.transpose (Torus.grad (u τ) y) i) =
        fun τ y => ∑ k ∈ Finset.univ, M₁.transpose i k * Torus.grad (u τ) y k :=
      funext fun τ => funext fun y => sa12x3w_matVec_apply _ _ _
    rw [e]
    exact sa12w2_CC_sum Finset.univ (fun k τ y => M₁.transpose i k * Torus.grad (u τ) y k)
      (fun k _ => sa12w2_CC_const_mul _ (hgrad k))
  have hH : ∀ i : Fin d, sa12w2_CC t (fun τ y => sa12w2_dens L (μ τ) y *
      (Torus.matVec M₁.transpose (Torus.grad (u τ) y)) i) := fun i => sa12w2_CC_mul hdens (hmv i)
  have hn : sa12w2_CC t (fun τ y => ∑ j ∈ Finset.univ, (convGradConv (periodicRieszGrad d s)
      (fun y => sa12w2_dens L (μ τ) y * (Torus.matVec M₁.transpose (Torus.grad (u τ) y)) j) y) j) :=
    sa12w2_CC_sum Finset.univ _ (fun j _ => sa12w2_CC_cgc hd hs0 hsd (hH j) j)
  refine ⟨_, sa12w2_CC_to_JC hn, fun τ hτ x => ?_⟩
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht⟩
  have hb := sa12w2_nonlocal_bridge hd hs0 hsd hL hγ M (hsm τ hτT) (hper τ hτT) (u τ) (hu.1 τ hτ) (L⁻¹ • x)
  have hx : L • L⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  rw [hx] at hb
  rw [hb]
  rfl

end HRS.PDE.SA12W2
