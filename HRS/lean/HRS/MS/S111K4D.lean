import HRS.MS.S111K4C

/-!
# S11.1 / T01 (S11K4), part D: variance of a centered Gaussian quadratic form on `ι → ℝ`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HRS.MS.S111K4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `HRS.quad_L2` for an arbitrary finite index type. -/
theorem k4_quad_L2_herm (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    ∫ g, (g ⬝ᵥ (M.mulVec g) - M.trace) ^ 2 ∂(k4gm ι) = HRS.vGauss * ∑ i, ∑ j, M i j ^ 2 := by
  classical
  set N := Fintype.card ι with hN
  let e : ι ≃ Fin N := Fintype.equivFin ι
  let M' : Matrix (Fin N) (Fin N) ℝ := M.submatrix e.symm e.symm
  have hM' : M'.IsHermitian := hM.submatrix e.symm
  have h := HRS.quad_L2 N M' hM'
  have hmp := measurePreserving_piCongrLeft (α := fun _ : Fin N => ℝ) (fun _ => gaussianReal 0 1) e
  have hΦ : ∀ (g : ι → ℝ) (k : Fin N), (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e) g k = g (e.symm k) := by
    intro g k
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hq : ∀ g : ι → ℝ, ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e) g) ⬝ᵥ
      (M'.mulVec ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) e) g)) - M'.trace =
        g ⬝ᵥ (M.mulVec g) - M.trace := by
    intro g
    simp only [hΦ, dotProduct, Matrix.mulVec, M', Matrix.submatrix_apply, Matrix.trace, Matrix.diag]
    have h1 : ∀ i, ∑ x, M i (e.symm x) * g (e.symm x) = ∑ j, M i j * g j :=
      fun i => Equiv.sum_comp e.symm (fun j => M i j * g j)
    simp only [h1]
    rw [Equiv.sum_comp e.symm (fun i => g i * ∑ j, M i j * g j), Equiv.sum_comp e.symm (fun i => M i i)]
  have hsum : ∑ k, ∑ l, M' k l ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
    simp only [M', Matrix.submatrix_apply]
    rw [Equiv.sum_comp e.symm (fun i => ∑ l, M i (e.symm l) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Equiv.sum_comp e.symm (fun j => M i j ^ 2)
  have hI := hmp.integral_comp' (g := fun z : Fin N → ℝ => (z ⬝ᵥ (M'.mulVec z) - M'.trace) ^ 2)
  rw [← hsum]
  have hpi : (k4gm ι) = Measure.pi (fun _ : ι => gaussianReal 0 1) := rfl
  rw [hpi]
  rw [← h] 
  rw [← hI]
  simp_rw [hq]

/-- For an arbitrary (not necessarily symmetric) matrix: `E (g·Mg - tr M)² ≤ 2 ‖M‖²_F`. -/
theorem k4_quad_L2_le (M : Matrix ι ι ℝ) :
    ∫ g, (g ⬝ᵥ (M.mulVec g) - M.trace) ^ 2 ∂(k4gm ι) ≤ 2 * k4fr M := by
  set Ms : Matrix ι ι ℝ := (1 / 2 : ℝ) • (M + Mᵀ) with hMs
  have hherm : Ms.IsHermitian := by
    ext i j
    simp [hMs, Matrix.conjTranspose_apply, add_comm]
  have hq : ∀ g : ι → ℝ, g ⬝ᵥ (Ms.mulVec g) = g ⬝ᵥ (M.mulVec g) := by
    intro g
    have e1 : g ⬝ᵥ (Mᵀ.mulVec g) = g ⬝ᵥ (M.mulVec g) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    simp only [hMs, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, e1]
    simp
    ring
  have ht : Ms.trace = M.trace := by
    simp [hMs, Matrix.trace_add, Matrix.trace_smul]
    ring
  have := k4_quad_L2_herm Ms hherm
  simp_rw [hq, ht] at this
  rw [this, HRS.vGauss_eq]
  have hfr : ∑ i, ∑ j, Ms i j ^ 2 ≤ k4fr M := by
    have : ∑ i, ∑ j, Ms i j ^ 2 ≤ ∑ i, ∑ j, ((M i j ^ 2 + M j i ^ 2) / 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        simp only [hMs, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
        nlinarith [sq_nonneg (M i j - M j i)]
    refine this.trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, k4fr]
    rw [Finset.sum_comm (f := fun i j => M j i ^ 2)]
    ring
  linarith

end HRS.MS.S111K4
