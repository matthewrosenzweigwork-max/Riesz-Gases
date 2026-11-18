import HRS.MC.S7PIF6B

/-!
# Packet piF6, part D: the algebra of the Itô drift on a piece

For `s ∈ (a,b]`: `itoDrift = ∂_r f + D f [b] + ½ ∑_k D² f [Φ_k, Φ_k]`; with the heat equation for `∂_r f` and the bracket
identity (F3) this is `-N^{-1/2} cylA_s + (2√N)⁻¹ cylJ_s`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

theorem S7PIF6_vec_expand {q : ℕ} (v : EuclideanSpace ℝ (Fin q)) :
    v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
  have := (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at this
  exact this.symm

theorem S7PIF6_lin_expand {q : ℕ} (L : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin q)) :
    L v = ∑ i, v i * L (EuclideanSpace.single i (1 : ℝ)) := by
  conv_lhs => rw [S7PIF6_vec_expand v]
  simp [map_sum, map_smul]

theorem S7PIF6_bilin_expand {q : ℕ} (B : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ)
    (u v : EuclideanSpace ℝ (Fin q)) :
    B u v = ∑ i, ∑ j, u i * v j * B (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  conv_lhs => rw [S7PIF6_vec_expand u]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S7PIF6_lin_expand (B (EuclideanSpace.single i 1)) v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- the algebra of the drift -/
theorem S7PIF6_drift_alg {q : ℕ} {ι : Type*} [Fintype ι] (F : EuclideanSpace ℝ (Fin q) → ℝ)
    (c : EuclideanSpace ℝ (Fin q)) (A e : Fin q → Fin q → ℝ) (Φ : ι → EuclideanSpace ℝ (Fin q))
    (bv : EuclideanSpace ℝ (Fin q)) (dt : ℝ)
    (hdt : dt = -(1 / 2) * ∑ i, ∑ j, A i j *
      iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
    (hbr : ∀ i j, ∑ k, Φ k i * Φ k j = A i j + e i j) :
    dt + fderiv ℝ F c bv + (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ F) c (Φ k) (Φ k) =
      ∑ i, bv i * fderiv ℝ F c (EuclideanSpace.single i 1) +
        (1 / 2) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
          e i j := by
  have h2 : ∀ u v : EuclideanSpace ℝ (Fin q), fderiv ℝ (fderiv ℝ F) c u v =
      ∑ i, ∑ j, u i * v j * iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
    intro u v
    rw [S7PIF6_bilin_expand (fderiv ℝ (fderiv ℝ F) c) u v]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  have h3 : ∑ k, fderiv ℝ (fderiv ℝ F) c (Φ k) (Φ k) =
      ∑ i, ∑ j, (A i j + e i j) *
        iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
    simp_rw [h2, ← hbr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [h3, S7PIF6_lin_expand (fderiv ℝ F c) bv, hdt]
  have h4 : ∑ i, ∑ j, (A i j + e i j) *
        iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] =
      ∑ i, ∑ j, A i j * iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
      ∑ i, ∑ j, iteratedFDeriv ℝ 2 F c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * e i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h4]
  ring

end HRS.MC.Sec7.S7PIF6

end
