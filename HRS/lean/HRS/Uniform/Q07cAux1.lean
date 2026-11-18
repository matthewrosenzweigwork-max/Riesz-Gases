import HRS.Uniform.Comparison
import HRS.Prob.MartingaleRep

/-!
# Q07c, part 1: operator theory (square-root uniqueness)
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section SqrtUnique

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An operator commuting with `D` commutes with every iterate `sqrtIter D n`. -/
lemma comm_sqrtIter {D X : H →L[ℝ] H} (h : X * D = D * X) : ∀ n, X * sqrtIter D n = sqrtIter D n * X
  | 0 => by simp [sqrtIter]
  | n + 1 => by
      have ih := comm_sqrtIter h n
      set Z := sqrtIter D n
      have e : X * (D + Z * Z) = (D + Z * Z) * X := by
        rw [mul_add, add_mul, h]
        congr 1
        calc X * (Z * Z) = (X * Z) * Z := (mul_assoc _ _ _).symm
          _ = (Z * X) * Z := by rw [ih]
          _ = Z * (X * Z) := mul_assoc _ _ _
          _ = Z * (Z * X) := by rw [ih]
          _ = (Z * Z) * X := (mul_assoc _ _ _).symm
      show X * ((1 / 2 : ℝ) • (D + Z * Z)) = ((1 / 2 : ℝ) • (D + Z * Z)) * X
      rw [mul_smul_comm, smul_mul_assoc, e]

lemma comm_sqrtLimOp {D X : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) (h : X * D = D * X) :
    X * sqrtLimOp D = sqrtLimOp D * X := by
  have h1 := tendsto_sqrtIter hD
  have h2 : Tendsto (fun n => X * sqrtIter D n) atTop (𝓝 (X * sqrtLimOp D)) :=
    (continuous_const.mul continuous_id).continuousAt.tendsto.comp h1
  have h3 : Tendsto (fun n => sqrtIter D n * X) atTop (𝓝 (sqrtLimOp D * X)) :=
    (continuous_id.mul continuous_const).continuousAt.tendsto.comp h1
  refine tendsto_nhds_unique h2 ?_
  simpa [comm_sqrtIter h] using h3


lemma isPSDOp_eq_zero_of_inner {S : H →L[ℝ] H} (hS : IsPSDOp S) {y : H} (hy : inner ℝ (S y) y = 0) :
    S y = 0 := by
  have h : ∀ z, inner ℝ (S y) z = 0 := fun z => by
    have := hS.cs y z
    rw [hy, zero_mul] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
  exact inner_self_eq_zero.1 (h (S y))

lemma unique_of_comm {S T : H →L[ℝ] H} (hS : IsPSDOp S) (hT : IsPSDOp T) (hc : S * T = T * S)
    (hsq : S * S = T * T) : S = T := by
  ext x
  set y : H := S x - T x with hy
  have h0 : (S + T) y = 0 := by
    have : (S + T) * (S - T) = 0 := by
      calc (S + T) * (S - T) = S * S - S * T + T * S - T * T := by noncomm_ring
        _ = 0 := by rw [hc, hsq]; abel
    have := congrArg (fun Z : H →L[ℝ] H => Z x) this
    simpa [hy] using this
  have h1 : inner ℝ (S y) y + inner ℝ (T y) y = 0 := by
    have : inner ℝ ((S + T) y) y = 0 := by rw [h0]; simp
    simpa [inner_add_left] using this
  have h2 : inner ℝ (S y) y = 0 := by
    linarith [hS.nonneg y, hT.nonneg y]
  have h3 : inner ℝ (T y) y = 0 := by
    linarith [hS.nonneg y, hT.nonneg y]
  have hSy := isPSDOp_eq_zero_of_inner hS h2
  have hTy := isPSDOp_eq_zero_of_inner hT h3
  have h4 : inner ℝ y y = 0 := by
    have : inner ℝ y y = inner ℝ (S x - T x) y := rfl
    rw [this, inner_sub_left, hS.symm, hT.symm, hSy, hTy]
    simp
  have := inner_self_eq_zero.1 h4
  exact sub_eq_zero.1 this

lemma sqrt_commutes {C : H →L[ℝ] H →L[ℝ] ℝ} {S : H →L[ℝ] H} (hS : IsSqrtOfForm S C) :
    formOp C = S * S := by
  ext x
  refine ext_inner_left ℝ fun y => ?_
  rw [real_inner_comm, inner_formOp]
  show C x y = inner ℝ y (S (S x))
  rw [← hS.symm y (S x), ← hS.sq x y, real_inner_comm]


lemma isPSDOp_of_sqrt {C : H →L[ℝ] H →L[ℝ] ℝ} {S : H →L[ℝ] H} (hS : IsSqrtOfForm S C) :
    IsPSDOp (formOp C) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [inner_formOp, real_inner_comm, inner_formOp, ← hS.sq, ← hS.sq, real_inner_comm]
  · rw [inner_formOp, ← hS.sq, real_inner_self_eq_norm_sq]; positivity

/-- Uniqueness of the nonnegative square root of a form. -/
theorem sqrt_unique {C : H →L[ℝ] H →L[ℝ] ℝ} {S S' : H →L[ℝ] H} (hS : IsSqrtOfForm S C)
    (hS' : IsSqrtOfForm S' C) : S = S' := by
  set A := formOp C with hA
  have hAp : IsPSDOp A := isPSDOp_of_sqrt hS
  set c : ℝ := ‖C‖ + 1 with hc
  have hc0 : 0 < c := by positivity
  have hAc : ∀ x, inner ℝ (A x) x ≤ c * ‖x‖ ^ 2 := by
    intro x
    rw [hA, inner_formOp]
    have h1 := C.le_opNorm₂ x x
    have h2 : (C x) x ≤ ‖C‖ * ‖x‖ * ‖x‖ := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h1)
    nlinarith [sq_nonneg ‖x‖, norm_nonneg C]
  obtain ⟨hS0p, hS0sq⟩ := sqrtOp_spec hAp hc0 hAc
  set S0 := sqrtOp c A with hS0
  have hD1 := norm_one_sub_inv_smul_le hAp hc0 hAc
  have key : ∀ X : H →L[ℝ] H, X * A = A * X → X * S0 = S0 * X := by
    intro X hX
    have hXD : X * ((1 : H →L[ℝ] H) - c⁻¹ • A) = ((1 : H →L[ℝ] H) - c⁻¹ • A) * X := by
      rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hX]; simp
    have := comm_sqrtLimOp hD1 hXD
    simp only [hS0, sqrtOp]
    rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, this]; simp
  have hAS : A = S * S := sqrt_commutes hS
  have hAS' : A = S' * S' := sqrt_commutes hS'
  have hSA : S * A = A * S := by rw [hAS]; simp [mul_assoc]
  have hSA' : S' * A = A * S' := by rw [hAS']; simp [mul_assoc]
  have e1 : S = S0 := unique_of_comm ⟨hS.symm, hS.nonneg⟩ hS0p (key S hSA) (by rw [hS0sq, ← hAS])
  have e2 : S' = S0 := unique_of_comm ⟨hS'.symm, hS'.nonneg⟩ hS0p (key S' hSA')
    (by rw [hS0sq, ← hAS'])
  rw [e1, e2]

end SqrtUnique

end HRS.Uniform.Q07c
