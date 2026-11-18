import HRS.MC.S7PIH2Gauss

/-!
# Packet piH, part 3: second order expansion of a Gaussian average
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

variable {q : ℕ}

theorem S7PIH_quad_expand (T : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ)
    (k : EuclideanSpace ℝ (Fin q)) :
    T k k = ∑ i, ∑ j, k i * k j * T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hk : ∀ x : EuclideanSpace ℝ (Fin q), x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) :=
    fun x => by
      ext l
      simp [Pi.single_apply]
  have e : T k k = T (∑ i, k i • EuclideanSpace.single i (1 : ℝ))
      (∑ j, k j • EuclideanSpace.single j (1 : ℝ)) := by rw [← hk k]
  rw [e]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem S7PIH_gauss_cross {Δ : Matrix (Fin q) (Fin q) ℝ} (hΔ : Δ.PosSemidef) (i j : Fin q) :
    Integrable (fun x : EuclideanSpace ℝ (Fin q) => x i * x j) (multivariateGaussian 0 Δ) ∧
      ∫ x : EuclideanSpace ℝ (Fin q), x i * x j ∂(multivariateGaussian 0 Δ) = Δ i j := by
  have hid : MemLp id 2 (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Δ) :=
    IsGaussian.memLp_two_id
  have hcoord : ∀ l : Fin q, MemLp (fun x : EuclideanSpace ℝ (Fin q) => x l) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Δ) := fun l =>
    (EuclideanSpace.proj (𝕜 := ℝ) l).comp_memLp' hid
  refine ⟨(hcoord i).integrable_mul (hcoord j), ?_⟩
  have hcov := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin q))) hΔ i j
  rw [covariance_eq_sub (hcoord i) (hcoord j)] at hcov
  have hm : ∀ l : Fin q, ∫ x : EuclideanSpace ℝ (Fin q), x l
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Δ) = 0 := fun l => by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin q) l)
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Δ) (φ := id)
      (IsGaussian.integrable_id)
    simpa using this
  rw [hm i, hm j, zero_mul, sub_zero] at hcov
  simpa [Pi.mul_apply] using hcov

theorem S7PIH_gauss_quad {Δ : Matrix (Fin q) (Fin q) ℝ} (hΔ : Δ.PosSemidef)
    (T : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ) :
    Integrable (fun k => T k k) (multivariateGaussian 0 Δ) ∧
      ∫ k, T k k ∂(multivariateGaussian 0 Δ) =
        ∑ i, ∑ j, Δ i j * T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hint : ∀ i j : Fin q, Integrable (fun a : EuclideanSpace ℝ (Fin q) =>
      a i * a j * T (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
      (multivariateGaussian 0 Δ) := fun i j =>
    (S7PIH_gauss_cross hΔ i j).1.mul_const _
  simp_rw [S7PIH_quad_expand T]
  constructor
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const, (S7PIH_gauss_cross hΔ i j).2]

end HRS.MC.Sec7.S7PIH

end
