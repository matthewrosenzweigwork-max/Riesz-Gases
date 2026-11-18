import HRS.MC.SEdgeVocab

/-!
# Packet B11b: Ornstein-Uhlenbeck wrapper around `stein_bounds`, `stein_equation`, `stein_third_derivative`
(relocated proof of `HRS.MC.SEdge.sed_B11b_ou`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B11b

open HRS HRS.Sec7

/-- decomposition of a vector in the standard basis -/
lemma b11b_decomp {p : ℕ} (z : EuclideanSpace ℝ (Fin p)) : z = ∑ a, z a • stdVec a := by
  ext i
  simp [stdVec, Finset.sum_apply, Pi.single_apply]

lemma b11b_lin {p : ℕ} (L : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) (z : EuclideanSpace ℝ (Fin p)) :
    L z = ∑ a, z a * L (stdVec a) := by
  conv_lhs => rw [b11b_decomp z]
  simp [map_sum]

lemma b11b_bil {p : ℕ} (M : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin p)) :
    M z z = ∑ a, ∑ b, z a * z b * M (stdVec a) (stdVec b) := by
  conv_lhs => rw [b11b_decomp z]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma b11b_mean {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (a : Fin p) :
    ∫ z : EuclideanSpace ℝ (Fin p), z a ∂(multivariateGaussian 0 C) = 0 := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) a).integral_comp_id_comm
    (μ := multivariateGaussian 0 C) IsGaussian.integrable_id
  simpa using h

lemma b11b_second_moment {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.PosSemidef) (a b : Fin p) :
    ∫ z : EuclideanSpace ℝ (Fin p), z a * z b ∂(multivariateGaussian 0 C) = C a b := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hC a b
  simpa [covariance, b11b_mean] using h

lemma b11b_integrable {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (a b : Fin p) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => z a * z b) (multivariateGaussian 0 C) := by
  have h : ∀ i : Fin p, MemLp (fun z : EuclideanSpace ℝ (Fin p) => z i) 2
      (multivariateGaussian 0 C) := fun i => by
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (IsGaussian.memLp_two_id
      (μ := multivariateGaussian 0 C))
    simpa using this
  exact (h a).integrable_mul (h b)

lemma b11b_isCentered {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) :
    IsCenteredGaussian (law (multivariateGaussian 0 C)
      (fun z : EuclideanSpace ℝ (Fin p) => z)) := by
  have hm : law (multivariateGaussian 0 C) (fun z : EuclideanSpace ℝ (Fin p) => z) =
      multivariateGaussian 0 C := Measure.map_id
  rw [hm]
  refine ⟨inferInstance, fun L => ?_⟩
  have h := L.integral_comp_id_comm (μ := multivariateGaussian 0 C) IsGaussian.integrable_id
  simpa using h

theorem sed_B11b_ou_proof {p : ℕ} (C : Matrix (Fin p) (Fin p) ℝ) (hC : C.PosSemidef)
    {F : EuclideanSpace ℝ (Fin p) → ℝ} (hF : MemCb 5 F) :
    ∃ f : EuclideanSpace ℝ (Fin p) → ℝ,
      f = steinSolution (multivariateGaussian 0 C) (fun z : EuclideanSpace ℝ (Fin p) => z) F ∧
      ContDiff ℝ 5 f ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤
        (j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j F y‖) ∧
      (∀ x, ∑ a, ∑ b, C a b * iteratedFDeriv ℝ 2 f x ![stdVec a, stdVec b] -
          ∑ a, x a * fderiv ℝ f x (stdVec a) = F x - ∫ z, F z ∂(multivariateGaussian 0 C)) ∧
      ∀ a b c, ∫ z, iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c]
          ∂(multivariateGaussian 0 C) =
        -(1 / 3) * ∫ z, iteratedFDeriv ℝ 3 F z ![stdVec a, stdVec b, stdVec c]
          ∂(multivariateGaussian 0 C) := by
  set P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) C with hP
  have hG : AEMeasurable (fun z : EuclideanSpace ℝ (Fin p) => z) P := aemeasurable_id
  have hGauss := b11b_isCentered C
  obtain ⟨-, hc5, hb⟩ := stein_bounds P (fun z : EuclideanSpace ℝ (Fin p) => z) hG hGauss F hF
  have heq := stein_equation P (fun z : EuclideanSpace ℝ (Fin p) => z) hG hGauss F hF
  refine ⟨_, rfl, hc5, hb, ?_, ?_⟩
  · intro x
    have h2 := heq x
    unfold covarianceContraction at h2
    have hf1 := b11b_lin (fderiv ℝ (steinSolution P (fun z : EuclideanSpace ℝ (Fin p) => z) F) x) x
    have hf2 : ∀ z : EuclideanSpace ℝ (Fin p),
        iteratedFDeriv ℝ 2 (steinSolution P (fun z : EuclideanSpace ℝ (Fin p) => z) F) x ![z, z] =
        ∑ a, ∑ b, z a * z b *
          iteratedFDeriv ℝ 2 (steinSolution P (fun z : EuclideanSpace ℝ (Fin p) => z) F) x
            ![stdVec a, stdVec b] := by
      intro z
      simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact b11b_bil _ z
    have hint : ∫ z : EuclideanSpace ℝ (Fin p),
        iteratedFDeriv ℝ 2 (steinSolution P (fun z : EuclideanSpace ℝ (Fin p) => z) F) x ![z, z]
          ∂P = ∑ a, ∑ b, C a b *
        iteratedFDeriv ℝ 2 (steinSolution P (fun z : EuclideanSpace ℝ (Fin p) => z) F) x
          ![stdVec a, stdVec b] := by
      simp_rw [hf2]
      rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ =>
        (b11b_integrable C a b).mul_const _))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finset_sum _ (fun b _ => (b11b_integrable C a b).mul_const _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, b11b_second_moment C hC]
    simp only [] at h2
    rw [hint, hf1] at h2
    exact h2
  · intro a b c
    exact stein_third_derivative P (fun z : EuclideanSpace ℝ (Fin p) => z) hG hGauss F hF
      ![stdVec a, stdVec b, stdVec c]


end HRS.MC.SEdge.B11b
