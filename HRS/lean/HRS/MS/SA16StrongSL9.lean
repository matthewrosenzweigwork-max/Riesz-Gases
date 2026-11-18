import HRS.MS.SA16StrongDefs

/-!
# S.A.16 SL9: `integrated_pairing_limit`

Uniform strong convergence and a common bound on `A` pass through the integrated weak equation.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

theorem integrated_pairing_limit
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → ℝ → X) (v : ℝ → X)
    (ℓ : X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ B)
    (hlim : StrongUniformLimit T u v)
    (hint : ∀ n, IntegrableOn (fun t => A t (u n t)) (Icc (0 : ℝ) T))
    (hvint : IntegrableOn (fun t => A t (v t)) (Icc (0 : ℝ) T))
    (heq : ∀ n, ∀ t ∈ Icc (0 : ℝ) T,
      ℓ (u n t)=ℓ (u n 0)+∫ r in Icc (0 : ℝ) t, A r (u n r)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ℓ (v t)=ℓ (v 0)+∫ r in Icc (0 : ℝ) t, A r (v r) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  set K : ℝ := ‖ℓ‖ + ‖ℓ‖ + B * t with hK
  have hK0 : 0 ≤ K := by
    have := norm_nonneg ℓ
    have := mul_nonneg hB ht.1
    linarith
  refine eq_of_forall_dist_le fun ε hε => ?_
  set ε' : ℝ := ε / (K + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨n, hn⟩ := hlim ε' hε'0
  have hn' : ∀ r ∈ Icc (0 : ℝ) T, ‖u n r - v r‖ < ε' := fun r hr => hn n le_rfl r hr
  -- the three pieces
  have e1 : |ℓ (v t) - ℓ (u n t)| ≤ ‖ℓ‖ * ε' := by
    rw [← map_sub, ← Real.norm_eq_abs]
    refine (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    exact (hn' t ht).le
  have e2 : |ℓ (u n 0) - ℓ (v 0)| ≤ ‖ℓ‖ * ε' := by
    rw [← map_sub, ← Real.norm_eq_abs]
    exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hn' 0 h0).le (norm_nonneg _))
  have e3 : |(∫ r in Icc (0 : ℝ) t, A r (u n r)) - ∫ r in Icc (0 : ℝ) t, A r (v r)| ≤
      B * ε' * t := by
    rw [← integral_sub ((hint n).mono_set hsub) (hvint.mono_set hsub), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := B * ε') (by simp [Real.volume_Icc])
      fun r hr => ?_).trans ?_
    · rw [← map_sub]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul (hA r (hsub hr)) (hn' r (hsub hr)).le (norm_nonneg _) hB
    · simp [Measure.real, Real.volume_Icc, ht.1]
  have hD : |ℓ (v t) - (ℓ (v 0) + ∫ r in Icc (0 : ℝ) t, A r (v r))| ≤ K * ε' := by
    have heqn := heq n t ht
    have : ℓ (v t) - (ℓ (v 0) + ∫ r in Icc (0 : ℝ) t, A r (v r)) =
        (ℓ (v t) - ℓ (u n t)) + (ℓ (u n 0) - ℓ (v 0)) +
          ((∫ r in Icc (0 : ℝ) t, A r (u n r)) - ∫ r in Icc (0 : ℝ) t, A r (v r)) := by
      rw [heqn]; ring
    rw [this]
    calc _ ≤ |ℓ (v t) - ℓ (u n t)| + |ℓ (u n 0) - ℓ (v 0)| +
          |(∫ r in Icc (0 : ℝ) t, A r (u n r)) - ∫ r in Icc (0 : ℝ) t, A r (v r)| :=
          (abs_add_three _ _ _)
      _ ≤ ‖ℓ‖ * ε' + ‖ℓ‖ * ε' + B * ε' * t := by linarith
      _ = K * ε' := by rw [hK]; ring
  rw [Real.dist_eq]
  refine hD.trans ?_
  rw [hε']
  calc K * (ε / (K + 1)) = (K / (K + 1)) * ε := by field_simp
    _ ≤ 1 * ε := by
        refine mul_le_mul_of_nonneg_right ?_ hε.le
        rw [div_le_one (by linarith)]; linarith
    _ = ε := one_mul ε

end HRS.Whole.AppendixA.Phase2SA16
