import HRS.MC.L2C6Aux1

/-!
# Packet L2C-6c, helper 1: the difference of two coordinates of a centred Gaussian vector

For `S` a matrix indexed by `Fin 1 ⊕ Fin 1`: the coordinates `s (inl 0) - s (inr 0)` are `MemLp 2` and
have second moment at most `max (S₁₁ + S₂₂ - 2 S₁₂) 0` under `multivariateGaussian 0 S`
(equality when `S` is positive semidefinite, `0` otherwise).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MC.L2C6c

abbrev PI := Fin 1 ⊕ Fin 1

theorem l2c6c_coord_memLp (S : Matrix PI PI ℝ) (i : PI) :
    MemLp (fun s : EuclideanSpace ℝ PI => s i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := by
  have := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ PI) S)
    (EuclideanSpace.proj i : StrongDual ℝ (EuclideanSpace ℝ PI)) 2 (by norm_num)
  simpa using this

theorem l2c6c_coord_mean (S : Matrix PI PI ℝ) (i : PI) :
    ∫ s : EuclideanSpace ℝ PI, s i ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S) = 0 := by
  have h := ContinuousLinearMap.integral_comp_comm
    (EuclideanSpace.proj i : EuclideanSpace ℝ PI →L[ℝ] ℝ)
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ PI) S))
  simp at h
  simpa using h

theorem l2c6c_coord_prod (S : Matrix PI PI ℝ) (hS : S.PosSemidef) (i j : PI) :
    ∫ s : EuclideanSpace ℝ PI, s i * s j
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S) = S i j := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ PI)) hS i j
  rw [covariance_eq_sub (l2c6c_coord_memLp S i) (l2c6c_coord_memLp S j), l2c6c_coord_mean,
    zero_mul, sub_zero] at h
  simpa using h

theorem l2c6c_gauss_pair (S : Matrix PI PI ℝ) :
    MemLp (fun s : EuclideanSpace ℝ PI => s (Sum.inl 0) - s (Sum.inr 0)) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) ∧
    ∫ s : EuclideanSpace ℝ PI, (s (Sum.inl 0) - s (Sum.inr 0)) ^ 2
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S) ≤
      max (S (Sum.inl 0) (Sum.inl 0) + S (Sum.inr 0) (Sum.inr 0) - 2 * S (Sum.inl 0) (Sum.inr 0)) 0 := by
  have ha := l2c6c_coord_memLp S (Sum.inl 0)
  have hb := l2c6c_coord_memLp S (Sum.inr 0)
  refine ⟨ha.sub hb, ?_⟩
  by_cases hS : S.PosSemidef
  · have e : ∀ s : EuclideanSpace ℝ PI, (s (Sum.inl 0) - s (Sum.inr 0)) ^ 2 =
        s (Sum.inl 0) * s (Sum.inl 0) + s (Sum.inr 0) * s (Sum.inr 0) -
          2 * (s (Sum.inl 0) * s (Sum.inr 0)) := fun s => by ring
    simp_rw [e]
    have i1 : Integrable (fun s : EuclideanSpace ℝ PI => s (Sum.inl 0) * s (Sum.inl 0))
        (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := ha.integrable_mul ha
    have i2 : Integrable (fun s : EuclideanSpace ℝ PI => s (Sum.inr 0) * s (Sum.inr 0))
        (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := hb.integrable_mul hb
    have i3 : Integrable (fun s : EuclideanSpace ℝ PI => 2 * (s (Sum.inl 0) * s (Sum.inr 0)))
        (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := (ha.integrable_mul hb).const_mul 2
    have k1 := l2c6c_coord_prod S hS (Sum.inl 0) (Sum.inl 0)
    have k2 := l2c6c_coord_prod S hS (Sum.inr 0) (Sum.inr 0)
    have k3 := l2c6c_coord_prod S hS (Sum.inl 0) (Sum.inr 0)
    have E : ∫ s : EuclideanSpace ℝ PI, (s (Sum.inl 0) * s (Sum.inl 0) + s (Sum.inr 0) * s (Sum.inr 0) -
          2 * (s (Sum.inl 0) * s (Sum.inr 0))) ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S) =
        (∫ s : EuclideanSpace ℝ PI, s (Sum.inl 0) * s (Sum.inl 0)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S)) +
        (∫ s : EuclideanSpace ℝ PI, s (Sum.inr 0) * s (Sum.inr 0)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S)) -
        2 * ∫ s : EuclideanSpace ℝ PI, s (Sum.inl 0) * s (Sum.inr 0)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := by
      have i12 : Integrable (fun s : EuclideanSpace ℝ PI =>
          s (Sum.inl 0) * s (Sum.inl 0) + s (Sum.inr 0) * s (Sum.inr 0))
          (multivariateGaussian (0 : EuclideanSpace ℝ PI) S) := i1.add i2
      rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul]
    have := le_max_left (S (Sum.inl 0) (Sum.inl 0) + S (Sum.inr 0) (Sum.inr 0) -
      2 * S (Sum.inl 0) (Sum.inr 0)) 0
    linarith
  · rw [multivariateGaussian_of_not_posSemidef _ hS]
    have : ∫ s : EuclideanSpace ℝ PI, (s (Sum.inl 0) - s (Sum.inr 0)) ^ 2
        ∂(Measure.dirac (0 : EuclideanSpace ℝ PI)) = 0 := by
      rw [integral_dirac' _ _ (by fun_prop)]
      simp
    rw [this]; exact le_max_right _ _

end HRS.MC.L2C6c
