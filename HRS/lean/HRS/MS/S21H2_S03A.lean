import HRS.Whole.Moving
import HRS.Whole.Thermal

/-!
# S21H2, packet R26-T3.S03 (part A): calculus helpers for the screened velocity

* `s21h2_s03_grad_norm`: `‖D^j (∇χ)‖ = ‖D^{j+1} χ‖` (the gradient is a linear isometry of `fderiv`).
* `s21h2_s03_lap`: the Laplacian as the trace of the second derivative in the standard basis.
* `s21h2_s03_movDiv`: `movDiv (ρ ∇χ) = ⟨∇ρ, ∇χ⟩ + ρ Δχ` for `ρ ∈ C¹`, `χ ∈ C²`.
Helper names carry the prefix `s21h2_s03_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem s21h2_s03_grad_norm {d j : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) χ)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ j (gradient χ) x‖ = ‖iteratedFDeriv ℝ (j + 1) χ x‖ := by
  have hfd : ContDiff ℝ (j : WithTop ℕ∞) (fderiv ℝ χ) := hχ.fderiv_right (m := j) (by norm_cast)
  have e : gradient χ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ χ := rfl
  rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem s21h2_s03_dual_comp {d : ℕ} (y : StrongDual ℝ (Euc d)) (i : Fin d) :
    (InnerProductSpace.toDual ℝ (Euc d)).symm y i = y (EuclideanSpace.single i 1) := by
  have h1 := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1) (y := y)
  have h2 := EuclideanSpace.inner_single_right i (1 : ℝ) ((InnerProductSpace.toDual ℝ (Euc d)).symm y)
  rw [← h1, h2]
  simp

theorem s21h2_s03_lap {d : ℕ} {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) (x : Euc d) :
    Laplacian.laplacian χ x =
      ∑ i : Fin d, fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := χ) (EuclideanSpace.basisFun (Fin d) ℝ)) x
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem s21h2_s03_movDiv {d : ℕ} {ρ χ : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hχ : ContDiff ℝ 2 χ)
    (x : Euc d) :
    movDiv (fun y => ρ y • gradient χ y) x =
      inner ℝ (gradient ρ x) (gradient χ x) + ρ x * Laplacian.laplacian χ x := by
  have hG1 : ContDiff ℝ 1 (gradient χ) := by
    have e : gradient χ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ χ := rfl
    rw [e]
    exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.contDiff).comp
      (hχ.fderiv_right (m := 1) (by norm_cast))
  have hGd : DifferentiableAt ℝ (gradient χ) x := hG1.differentiable (by norm_num) x
  have hρd : DifferentiableAt ℝ ρ x := hρ.differentiable (by norm_num) x
  have hF : fderiv ℝ (fun y => ρ y • gradient χ y) x =
      ρ x • fderiv ℝ (gradient χ) x + (fderiv ℝ ρ x).smulRight (gradient χ x) :=
    fderiv_smul hρd hGd
  -- derivative of the gradient in the standard basis
  have hD : ∀ i : Fin d, fderiv ℝ (gradient χ) x (EuclideanSpace.single i 1) =
      (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ (fderiv ℝ χ) x (EuclideanSpace.single i 1)) := by
    intro i
    have e : gradient χ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ χ := rfl
    have hL : HasFDerivAt ((InnerProductSpace.toDual ℝ (Euc d)).symm : StrongDual ℝ (Euc d) → Euc d)
        ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.toContinuousLinearMap) (fderiv ℝ χ x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    have hT : HasFDerivAt (fderiv ℝ χ) (fderiv ℝ (fderiv ℝ χ) x) x :=
      ((hχ.fderiv_right (m := 1) (by norm_cast)).differentiable (by norm_num) x).hasFDerivAt
    have := (hL.comp x hT).fderiv
    rw [e, this]
    rfl
  unfold movDiv
  rw [hF]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, hD, s21h2_s03_dual_comp]
  rw [s21h2_s03_lap hχ x]
  rw [add_comm]
  congr 1
  have hgr : ∀ i : Fin d, (gradient ρ x).ofLp i = fderiv ℝ ρ x (EuclideanSpace.single i 1) :=
    fun i => s21h2_s03_dual_comp (fderiv ℝ ρ x) i
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hgr]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end HRS.MS.R26T3
