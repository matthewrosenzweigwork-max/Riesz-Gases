import HRS.Uniform.Q45Cov9
import HRS.Uniform.Q07cAux1

/-!
# Q45 (Lemma 3.20): Jordan decomposition of a self-adjoint trace-norm form, operator algebra

Given a symmetric bounded form `D = ⟨A·,·⟩` and a nonnegative operator `S` with `S² = A²` commuting with `A`
(`S = |A|`), the operators `P = (S + A)/2`, `N = (S - A)/2` are nonnegative, `PN = NP = 0`, `P - N = A`.
-/

noncomputable section

open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Alg

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The form `(x,y) ↦ ⟨T x, y⟩` of an operator. -/
def formOfOp (T : H →L[ℝ] H) : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T

lemma formOfOp_apply (T : H →L[ℝ] H) (x y : H) : formOfOp T x y = inner ℝ (T x) y := rfl

variable {S A : H →L[ℝ] H}

section
variable (hS : IsPSDOp S) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
  (hSS : S * S = A * A) (hSA : S * A = A * S)
include hSS hSA

lemma pn_zero : ((1 / 2 : ℝ) • (S + A)) * ((1 / 2 : ℝ) • (S - A)) = 0 := by
  rw [smul_mul_smul_comm]
  have : (S + A) * (S - A) = 0 := by
    rw [mul_sub, add_mul, add_mul, hSS, hSA]
    abel
  rw [this]; simp

lemma np_zero : ((1 / 2 : ℝ) • (S - A)) * ((1 / 2 : ℝ) • (S + A)) = 0 := by
  rw [smul_mul_smul_comm]
  have : (S - A) * (S + A) = 0 := by
    rw [mul_add, sub_mul, sub_mul, hSS, hSA]
    abel
  rw [this]; simp

end

lemma psd_of_mul_zero {P N : H →L[ℝ] H} (hPs : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hNs : ∀ x y, inner ℝ (N x) y = inner ℝ x (N y)) (hSnn : ∀ x, 0 ≤ inner ℝ ((P + N) x) x)
    (hPN : P * N = 0) : IsPSDOp P := by
  refine ⟨hPs, fun x => ?_⟩
  set K : Submodule ℝ H := LinearMap.ker (P : H →ₗ[ℝ] H) with hK
  haveI : CompleteSpace K := (P.isClosed_ker).completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  set x₂ : H := K.starProjection x with hx₂
  set x₁ : H := x - x₂ with hx₁
  have hx₂K : x₂ ∈ K := Submodule.starProjection_apply_mem K x
  have hx₁K : x₁ ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hPx₂ : P x₂ = 0 := hx₂K
  have hxx : x = x₁ + x₂ := by simp [hx₁]
  have hNx₁ : N x₁ = 0 := by
    refine ext_inner_right ℝ fun y => ?_
    rw [hNs, inner_zero_left]
    have : N y ∈ K := by
      show P (N y) = 0
      have := congrArg (fun T : H →L[ℝ] H => T y) hPN
      simpa using this
    exact Submodule.inner_left_of_mem_orthogonal this hx₁K
  have e1 : inner ℝ (P x) x = inner ℝ (P x₁) x₁ := by
    have h1 : P x = P x₁ := by rw [hxx, map_add, hPx₂, add_zero]
    have h2 : inner ℝ (P x₁) x₂ = 0 := by rw [hPs, hPx₂, inner_zero_right]
    rw [h1]
    conv_lhs => rw [hxx]
    rw [inner_add_right, h2, add_zero]
  rw [e1]
  have := hSnn x₁
  simpa [hNx₁] using this

lemma psd_of_mul_zero' {P N : H →L[ℝ] H} (hPs : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hNs : ∀ x y, inner ℝ (N x) y = inner ℝ x (N y)) (hSnn : ∀ x, 0 ≤ inner ℝ ((P + N) x) x)
    (hNP : N * P = 0) : IsPSDOp N := by
  refine psd_of_mul_zero hNs hPs (fun x => ?_) hNP
  simpa [add_comm] using hSnn x

lemma isPSD_pn (hS : IsPSDOp S) (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hSS : S * S = A * A) (hSA : S * A = A * S) :
    IsPSDOp ((1 / 2 : ℝ) • (S + A)) ∧ IsPSDOp ((1 / 2 : ℝ) • (S - A)) := by
  have hPs : ∀ x y, inner ℝ (((1 / 2 : ℝ) • (S + A)) x) y = inner ℝ x (((1 / 2 : ℝ) • (S + A)) y) := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_left,
      inner_add_left, inner_smul_right, inner_add_right, hS.symm x y, hA x y, conj_trivial]
  have hNs : ∀ x y, inner ℝ (((1 / 2 : ℝ) • (S - A)) x) y = inner ℝ x (((1 / 2 : ℝ) • (S - A)) y) := by
    intro x y
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_left,
      inner_sub_left, inner_smul_right, inner_sub_right, hS.symm x y, hA x y, conj_trivial]
  have hsum : (1 / 2 : ℝ) • (S + A) + (1 / 2 : ℝ) • (S - A) = S := by
    ext x; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply]; module
  have hSnn : ∀ x, 0 ≤ inner ℝ (((1 / 2 : ℝ) • (S + A) + (1 / 2 : ℝ) • (S - A)) x) x := by
    intro x; rw [hsum]; exact hS.nonneg x
  exact ⟨psd_of_mul_zero hPs hNs hSnn (pn_zero hSS hSA),
    psd_of_mul_zero' hPs hNs hSnn (np_zero hSS hSA)⟩

end Alg

end HRS.Uniform.Q45
