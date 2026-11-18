import Mathlib
import HRS.MC.Sec7Vocab

/-!
# Packet `s7_E4_normalized_clt`, file 1: spectral reduction of a Gaussian quadratic form

For a positive semidefinite `C` and a symmetric `H` (finite matrices) the centred quadratic form
`z |-> (1/2) sum_ij H_ij (z_i z_j - C_ij)` of `N(0,C)` has the law of `(1/2) sum_k a_k (y_k^2 - 1)`,
`y` iid standard Gaussian, `a_k` the eigenvalues of `C^{1/2} H C^{1/2}`; the eigenvalues are bounded by
the quadratic form bound of `H` when `C <= 1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.E4A1

variable {L : ℕ}

/-- the quadratic form on the Gaussian vector -/
def psi (C H : Matrix (Fin L) (Fin L) ℝ) (z : EuclideanSpace ℝ (Fin L)) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, H i j * (z i * z j - C i j)

theorem psi_meas (C H : Matrix (Fin L) (Fin L) ℝ) : Measurable (psi C H) := by
  unfold psi; fun_prop

theorem sum_quad (H : Matrix (Fin L) (Fin L) ℝ) (u : Fin L → ℝ) :
    ∑ i, ∑ j, H i j * (u i * u j) = u ⬝ᵥ H *ᵥ u := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psi_eq (C H : Matrix (Fin L) (Fin L) ℝ) (z : EuclideanSpace ℝ (Fin L)) :
    psi C H z = (1 / 2 : ℝ) * ((z.ofLp ⬝ᵥ H *ᵥ z.ofLp) - ∑ i, ∑ j, H i j * C i j) := by
  unfold psi
  have : ∀ i j, H i j * (z i * z j - C i j) = H i j * (z i * z j) - H i j * C i j := fun i j => by ring
  simp only [this, Finset.sum_sub_distrib]
  rw [sum_quad]


theorem quad_conj (R M : Matrix (Fin L) (Fin L) ℝ) (hRt : Rᵀ = R) (v : Fin L → ℝ) :
    (R *ᵥ v) ⬝ᵥ (M *ᵥ (R *ᵥ v)) = v ⬝ᵥ ((R * M * R) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose R v,
    Matrix.vecMul_vecMul, hRt, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  simp [Matrix.vecMul_vecMul, Matrix.mul_assoc]


section Spectral

variable {A : Matrix (Fin L) (Fin L) ℝ}

theorem eig_dot (hA : A.IsHermitian) (k l : Fin L) :
    (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L)).ofLp ⬝ᵥ
      (hA.eigenvectorBasis l : EuclideanSpace ℝ (Fin L)).ofLp = if k = l then 1 else 0 := by
  have hon := hA.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at hon
  have := hon k l
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [dotProduct_comm] using this

theorem eig_mul (hA : A.IsHermitian) (l : Fin L) :
    A *ᵥ (hA.eigenvectorBasis l : EuclideanSpace ℝ (Fin L)).ofLp =
      hA.eigenvalues l • (hA.eigenvectorBasis l : EuclideanSpace ℝ (Fin L)).ofLp := by
  have := hA.mulVec_eigenvectorBasis l
  simpa using this

theorem eig_quad (hA : A.IsHermitian) (y : Fin L → ℝ) :
    (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L))).ofLp ⬝ᵥ
      A *ᵥ (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L))).ofLp =
      ∑ k, hA.eigenvalues k * y k ^ 2 := by
  have hdot := eig_dot hA
  have hmul := eig_mul hA
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, hmul,
    sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, hdot]
  simp [Finset.sum_ite_eq, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Spectral

theorem reduce {C H : Matrix (Fin L) (Fin L) ℝ} (hC : C.PosSemidef) (hH : Hᵀ = H) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hq : ∀ z : Fin L → ℝ, |z ⬝ᵥ H *ᵥ z| ≤ Λ * (z ⬝ᵥ z))
    (hCle : ∀ z : Fin L → ℝ, z ⬝ᵥ C *ᵥ z ≤ z ⬝ᵥ z) :
    ∃ a : Fin L → ℝ, (∀ k, |a k| ≤ Λ) ∧
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) C).map (psi C H) =
        (Measure.pi fun _ : Fin L => gaussianReal 0 1).map
          (fun y : Fin L → ℝ => (1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) := by
  set R : Matrix (Fin L) (Fin L) ℝ := CFC.sqrt C with hR
  have hRR : R * R = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  have hRt : Rᵀ = R := by
    have : IsSelfAdjoint R := (CFC.sqrt_nonneg C).isSelfAdjoint
    simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this
  set A : Matrix (Fin L) (Fin L) ℝ := R * H * R with hAdef
  have hA : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hAdef, Matrix.transpose_mul, Matrix.transpose_mul,
      hRt, hH, Matrix.mul_assoc]
  have hCt : Cᵀ = C := by
    have := hC.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  -- the trace identity
  have htr : ∑ i, ∑ j, H i j * C i j = ∑ k, hA.eigenvalues k := by
    have h1 : ∑ i, ∑ j, H i j * C i j = (H * Cᵀ).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    have h2 : (H * C).trace = A.trace := by
      rw [hAdef, ← hRR, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have h3 := hA.trace_eq_sum_eigenvalues
    simp at h3
    rw [h1, hCt, h2, h3]
  have hlaw : multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) C =
      (Measure.pi fun _ : Fin L => gaussianReal 0 1).map (fun y : Fin L → ℝ =>
        Matrix.toEuclideanCLM (𝕜 := ℝ) R (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L)))) := by
    unfold multivariateGaussian
    rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis, Measure.map_map (by fun_prop)
      (by fun_prop)]
    congr 1
    funext y
    simp [hR]
  have hpt : ∀ y : Fin L → ℝ, psi C H (Matrix.toEuclideanCLM (𝕜 := ℝ) R
      (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L)))) =
      (1 / 2 : ℝ) * ∑ k, hA.eigenvalues k * (y k ^ 2 - 1) := by
    intro y
    rw [psi_eq]
    have e1 : (Matrix.toEuclideanCLM (𝕜 := ℝ) R (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L)))).ofLp
        = R *ᵥ (∑ k, y k • (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L))).ofLp := by
      simp [Matrix.mulVec_sum, Matrix.mulVec_smul]
    rw [e1, quad_conj R H hRt, ← hAdef, eig_quad hA, htr]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  refine ⟨hA.eigenvalues, fun k => ?_, ?_⟩
  · have hbb := eig_dot hA k k
    have hm := eig_mul hA k
    set bv := (hA.eigenvectorBasis k : EuclideanSpace ℝ (Fin L)).ofLp with hbv
    simp only [ite_true] at hbb
    have h1 : hA.eigenvalues k = bv ⬝ᵥ A *ᵥ bv := by
      rw [hm, dotProduct_smul, hbb]; simp
    have h2 : bv ⬝ᵥ A *ᵥ bv = (R *ᵥ bv) ⬝ᵥ H *ᵥ (R *ᵥ bv) := (quad_conj R H hRt bv).symm
    have h3 : (R *ᵥ bv) ⬝ᵥ (R *ᵥ bv) = bv ⬝ᵥ C *ᵥ bv := by
      have := quad_conj R 1 hRt bv
      rw [Matrix.one_mulVec, Matrix.mul_one, hRR] at this
      exact this
    have h4 := hq (R *ᵥ bv)
    have h5 := hCle bv
    rw [h1, h2]
    refine h4.trans ?_
    rw [h3]
    nlinarith
  · rw [hlaw, Measure.map_map (psi_meas C H) (by fun_prop)]
    congr 1
    funext y
    exact hpt y

end HRS.MC.Sec7.E4A1

end
