import HRS.MS.WsInitGAux9

/-!
# S21 packet G, part 10: finite-dimensional laws of a centred Gaussian on a Hilbert space

`s21g_fdd_gaussian`: for a centred Gaussian `γ` on a separable Hilbert space `V` and vectors `w_1, ..., w_p`, the matrix
`M_{ij} = Cov_γ(w_i, w_j)` is positive semidefinite and `γ.map (x ↦ (⟨w_i,x⟩)_i) = multivariateGaussian 0 M`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S21

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

/-- The map `x ↦ (⟨w_a, x⟩)_a`. -/
def s21gAw {p : ℕ} (w : Fin p → V) : V →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ∑ a : Fin p, (innerSL ℝ (w a)).smulRight (EuclideanSpace.single a (1 : ℝ))

theorem s21gAw_apply {p : ℕ} (w : Fin p → V) (x : V) (a : Fin p) : s21gAw w x a = inner ℝ (w a) x := by
  simp [s21gAw, Pi.single_apply]

theorem s21gAw_adjoint {p : ℕ} (w : Fin p → V) (u : EuclideanSpace ℝ (Fin p)) :
    (s21gAw w).adjoint u = ∑ a, u a • w a := by
  refine ext_inner_right ℝ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner]
  simp only [inner_smul_left, s21gAw_apply, PiLp.inner_apply]
  simp [mul_comm]

theorem s21g_cov_sum (γ : Measure V) {p : ℕ} (w : Fin p → V) (u v : Fin p → ℝ) :
    covarianceBilin γ (∑ i, u i • w i) (∑ j, v j • w j) =
      ∑ i, ∑ j, u i * v j * covarianceBilin γ (w i) (w j) := by
  rw [map_sum (covarianceBilin γ), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]; ring

theorem s21g_fdd_gaussian (γ : Measure V) [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) {p : ℕ} (w : Fin p → V) :
    (Matrix.of fun i j => covarianceBilin γ (w i) (w j)).PosSemidef ∧
      γ.map (s21gAw w) = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
        (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) := by
  have hPSD : (Matrix.of fun i j => covarianceBilin γ (w i) (w j)).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, covarianceBilin_comm (w i) (w j)]
    · have h := covarianceBilin_self_nonneg (μ := γ) (∑ i, x i • w i)
      rw [s21g_cov_sum] at h
      convert h using 1
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  refine ⟨hPSD, ?_⟩
  have hGA : IsGaussian (γ.map (s21gAw w)) := inferInstance
  have hmA : (γ.map (s21gAw w))[id] = 0 := by
    show ∫ z, id z ∂(γ.map (s21gAw w)) = 0
    rw [integral_map (s21gAw w).continuous.aemeasurable aestronglyMeasurable_id]
    simp only [id]
    rw [(s21gAw w).integral_comp_id_comm IsGaussian.integrable_id]
    simp only [id] at hmean
    rw [hmean, map_zero]
  refine IsGaussian.ext (hmA.trans integral_id_multivariateGaussian'.symm) ?_
  ext u v
  rw [covarianceBilin_multivariateGaussian hPSD, covarianceBilin_map IsGaussian.memLp_two_id]
  show covarianceBilin γ ((s21gAw w).adjoint u) ((s21gAw w).adjoint v) = _
  rw [s21gAw_adjoint, s21gAw_adjoint, s21g_cov_sum]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end HRS.MS.S21
