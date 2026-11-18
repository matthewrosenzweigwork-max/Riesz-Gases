import HRS.MS.SA16Y10Nd3
import HRS.MS.SA16Y4Ap2

/-!
# S.A.16 (SA16Y10) Gi1: `sa16y10_GInt_diff_sub` (stability G3(a), sub regime)

`‖(GInt μ₁ σ - GInt μ₂ σ) ∘ ι²‖_{W^{m+2}→W^m} ≤ K δ` for the interpolated mollified nonlocal operators of two density
families (the operators `T0` of `sa16y4_approx2`), `δ` the weighted `C^{m+2}` size of `μ₁ r - μ₂ r`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sa16y10_GInt_diff_sub (d m : ℕ) (hd : 2 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ μ₁ μ₂ : ℝ → Euc d → ℝ,
      (∀ r ∈ Set.Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ₁ r)) →
      (∀ r ∈ Set.Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ₂ r)) →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ κ ≤ m + 2, ∀ x,
        ‖iteratedFDeriv ℝ κ (fun y => μ₁ r y - μ₂ r y) x‖ ≤ δ * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Set.Icc (0 : ℝ) t,
        ‖(sa16y4_GInt d m N p s M t μ₁ σ - sa16y4_GInt d m N p s M t μ₂ σ).comp (sa16sz_iota2 d m p)‖ ≤ K * δ := by
  obtain ⟨K, hK, hnode⟩ := sa16y10_node_diff_sub d m hd s p MB Λ hs0 hs2 hfar
  refine ⟨K, hK, fun t ht M hM μ₁ μ₂ h1 h2 δ hδ hdec N hN σ hσ => ?_⟩
  set X : ℕ → WmpSpace d (m + 2) p →L[ℝ] WmpSpace d m p := fun i =>
    (sa16so_G d m p s M (sa16q_mol N (μ₁ (t - (i : ℝ) * t / N))) -
      sa16so_G d m p s M (sa16q_mol N (μ₂ (t - (i : ℝ) * t / N)))).comp (sa16sz_iota2 d m p) with hX
  have hsum : (sa16y4_GInt d m N p s M t μ₁ σ - sa16y4_GInt d m N p s M t μ₂ σ).comp (sa16sz_iota2 d m p) =
      ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ • X i := by
    unfold sa16y4_GInt
    ext1 G
    simp only [hX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.smul_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]
  have hXn : ∀ i ∈ Finset.range (N + 1), ‖X i‖ ≤ K * δ := fun i hi => by
    have hmem := sa16y4_node_mem hN ht hi
    exact hnode M hM _ _ (h1 _ hmem) (h2 _ hmem) δ hδ (hdec _ hmem) N
  have hw1 : ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ = 1 := sa16y4_hat_sum hN ht hσ
  rw [hsum]
  refine le_trans (norm_sum_le (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ • X i)) ?_
  calc ∑ i ∈ Finset.range (N + 1), ‖sa16y4_hat N t i σ • X i‖
      ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (K * δ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        rw [Real.norm_of_nonneg (sa16y4_hat_nonneg N t i σ)]
        exact mul_le_mul_of_nonneg_left (hXn i hi) (sa16y4_hat_nonneg N t i σ)
    _ = K * δ := by rw [← Finset.sum_mul, hw1, one_mul]

end HRS.Whole.AppendixA.Phase2SA16R

end
