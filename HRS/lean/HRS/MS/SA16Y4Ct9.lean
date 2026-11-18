import HRS.MS.SA16Y4Ct8

/-!
# S.A.16 (SA16Y4) Ct9: duality of the mollifier for locally integrable functions

`sa16y4_mol_dual_loc`: `∫ (ρ_n ⋆ f) g = ∫ f (ρ_n ⋆ g)` for `f` locally integrable and `g ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct9
variable {d : ℕ}

theorem sa16y4_mol_dual_loc (n : ℕ) {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : LocallyIntegrable f volume) (hg : IsCcInfty g) :
    ∫ x, sa16q_mol n f x * g x = ∫ x, f x * sa16q_mol n g x := by
  have hρc : Continuous (sa16y_rho d n) := (sa16y_rho_smooth n).continuous
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ x ∈ tsupport g, ‖x‖ ≤ R₀ := by
    obtain ⟨R, hR⟩ := hg.2.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
    exact ⟨R, fun x hx => by simpa using hR hx⟩
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 (R₀ + 1) with hB
  set f' : EuclideanSpace ℝ (Fin d) → ℝ := B.indicator f with hf'
  have hf'i : Integrable f' volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hf.integrableOn_isCompact (isCompact_closedBall _ _))
  set H : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun q => f q.2 * sa16y_rho d n (q.1 - q.2) * g q.1 with hH
  have hHeq : H = fun q => g q.1 * ((ContinuousLinearMap.mul ℝ ℝ) (f' q.2) (sa16y_rho d n (q.1 - q.2))) := by
    funext q
    simp only [hH, hf', ContinuousLinearMap.mul_apply']
    by_cases h1 : g q.1 = 0
    · simp [h1]
    by_cases h2 : sa16y_rho d n (q.1 - q.2) = 0
    · simp [h2]
    have hx : ‖q.1‖ ≤ R₀ := hR₀ _ (subset_tsupport _ h1)
    have hy : ‖q.1 - q.2‖ ≤ 1 / ((n : ℝ) + 1) := by
      by_contra h; exact h2 (sa16y_rho_supp n _ (not_le.1 h))
    have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hyB : q.2 ∈ B := by
      rw [hB, mem_closedBall_zero_iff]
      calc ‖q.2‖ = ‖q.1 - (q.1 - q.2)‖ := by congr 1; abel
        _ ≤ ‖q.1‖ + ‖q.1 - q.2‖ := norm_sub_le _ _
        _ ≤ R₀ + 1 := by linarith
    rw [Set.indicator_of_mem hyB]; ring
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
    exact ⟨C, hC⟩
  have hHi : Integrable H (volume.prod volume) := by
    rw [hHeq]
    exact (Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf'i
      (sa16y_rho_integrable (d := d) n)).bdd_mul
      (hg.1.continuous.comp continuous_fst).aestronglyMeasurable (Eventually.of_forall fun q => hC _)
  have e1 : ∫ x, sa16q_mol n f x * g x = ∫ x, ∫ y, H (x, y) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [sa16q_mol_eq]
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hH, sa16q_rhoS_apply]
  have e2 : ∫ x, f x * sa16q_mol n g x = ∫ y, ∫ x, H (x, y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [sa16q_mol_eq]
    dsimp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : sa16y_rho d n (y - x) = sa16y_rho d n (x - y) := by
      rw [← neg_sub, sa16y4_rho_even]
    simp only [hH, sa16q_rhoS_apply, this]; ring
  rw [e1, e2]
  exact integral_integral_swap hHi
end Ct9

end HRS.Whole.AppendixA.Phase2SA16R
