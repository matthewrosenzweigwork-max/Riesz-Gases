import HRS.MS.SA12V3F

/-!
# S.A.12 N1/N2 (SA12V3 worker), part G: derivatives of `γ * ψ` and the expansion of the nonlocal test term
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_H_eq_conv (γ ψ : Euc d → ℝ) :
    sa12vH γ ψ = HRS.MH.AdjointRd.Phase2SA12Near.sa12n_conv γ ψ := by
  funext w
  unfold sa12vH HRS.MH.AdjointRd.Phase2SA12Near.sa12n_conv
  rw [← integral_sub_left_eq_self (fun y => γ y * ψ (w - y)) volume w]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp

theorem sa12v3_H_partial {γ ψ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (sa12vH γ ψ) ∧ ∀ {k : ℕ} (idx : Fin k → Fin d) (x : Euc d),
      partialDeriv idx (sa12vH γ ψ) x = sa12vH γ (partialDeriv idx ψ) x := by
  obtain ⟨h1, h2⟩ := HRS.MH.AdjointRd.Phase2SA12Near.sa12n_conv_partial hγ hψ hψc
  rw [sa12v3_H_eq_conv]
  refine ⟨h1, fun idx x => ?_⟩
  rw [h2 idx x, sa12v3_H_eq_conv]

theorem sa12v3_fderiv_H {γ ψ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (y : Euc d) (j : Fin d) :
    fderiv ℝ (sa12vH γ ψ) y (EuclideanSpace.single j (1 : ℝ)) = sa12vH γ (sa12v3_D1 ψ j) y := by
  have h := (sa12v3_H_partial hγ hψ hψc).2 (fun _ : Fin 1 => j) y
  rw [sa12v_partialDeriv_one] at h
  rw [h]
  have : partialDeriv (fun _ : Fin 1 => j) ψ = sa12v3_D1 ψ j := by
    funext z; rw [sa12v_partialDeriv_one]; rfl
  rw [this]

/-- The nonlocal test term for an arbitrary kernel (the common shape of `nonlocalTestPer` and `nonlocalTestRd`). -/
def sa12v3_NT (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i *
    partialDeriv (fun _ : Fin 1 => j) (fun y => μ y * gradient (fun w => ∫ u, γ (w - u) * ψ u) y i) x

theorem sa12v3_per_eq (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ ψ : Euc d → ℝ) (x : Euc d) :
    nonlocalTestPer L γ M μ ψ x = sa12v3_NT γ M μ ψ x := rfl

theorem sa12v3_rd_eq (C : WholeCoeff d) (τ' : ℝ) (ψ : Euc d → ℝ) (x : Euc d) :
    nonlocalTestRd C τ' ψ x = sa12v3_NT (rieszKernel d C.s) C.M (C.ρ τ') ψ x := rfl

theorem sa12v3_NT_expand {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (M : Matrix (Fin d) (Fin d) ℝ)
    {μ ψ : Euc d → ℝ} (hμ : Differentiable ℝ μ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (x : Euc d) :
    sa12v3_NT γ M μ ψ x = ∑ i : Fin d, ∑ j : Fin d, M j i *
      (fderiv ℝ μ x (EuclideanSpace.single j (1 : ℝ)) * sa12vH γ (sa12v3_D1 ψ i) x +
        μ x * sa12vH γ (sa12v3_D1 (sa12v3_D1 ψ i) j) x) := by
  unfold sa12v3_NT
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  congr 1
  have e1 : (fun y => μ y * gradient (fun w => ∫ u, γ (w - u) * ψ u) y i) =
      fun y => μ y * sa12vH γ (sa12v3_D1 ψ i) y := by
    funext y
    rw [sa12v_grad_coord]
    exact congrArg (μ y * ·) (sa12v3_fderiv_H hγ hψ hψc y i)
  rw [e1, sa12v_partialDeriv_one]
  have hDi : ContDiff ℝ ∞ (sa12v3_D1 ψ i) := sa12v3_D1_smooth hψ i
  have hDic : HasCompactSupport (sa12v3_D1 ψ i) := sa12v3_D1_compact hψc i
  have hHi : Differentiable ℝ (sa12vH γ (sa12v3_D1 ψ i)) :=
    ((sa12v_H_smooth hγ hDi hDic).differentiable (by simp))
  rw [fderiv_fun_mul (hμ x) (hHi x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sa12v3_fderiv_H hγ hDi hDic x j]
  ring

end HRS.MH.AdjointRd.Phase2SA12V3
