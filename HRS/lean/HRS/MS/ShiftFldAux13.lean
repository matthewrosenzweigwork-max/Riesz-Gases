import HRS.MS.ShiftFldAux12

/-!
# S79P: `∑_i ∫ ∂_i u ρ (∂_i g*ψ) = ∫ (g*ψ) ρ 𝒜u`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.S21 HRS.MH.DualityRd HRS.MS.UniqT3 HRS.MS.UniqNDefs HRS.Whole.AppendixALemmas
open HRS (Euc)

variable {d : ℕ}

theorem s79g_nlw2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∑ i : Fin d, ∫ x, D1 i u x * (thermalDensity d s a β x * kernelConvDeriv d s i ψ x) =
      ∫ x, HRS.Whole.convFun (rieszKernel d s) ψ x * (thermalDensity d s a β x *
        Aop d s a β (thermalDensity d s a β) u x) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 1) (by norm_num)
  have hD1u : ∀ i x, |D1 i u x| ≤ B1 := fun i x =>
    (HRS.MS.UniqN2b.n2b_D1_le i u x).trans (by have := hB1 x; rwa [norm_iteratedFDeriv_one] at this)
  obtain ⟨B2, hB20, hB2⟩ := s79g_D1D1_bound hu
  obtain ⟨C0, hC0⟩ := conv_bound hs0 hsd hψ.continuous hψc
  have hC00 : 0 ≤ C0 := by
    have := hC0 (0 : Euc d); simp only [norm_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  set Θ := HRS.Whole.convFun (rieszKernel d s) ψ with hΘ
  have hΘd : Differentiable ℝ Θ := convFun_diff hl hψ1 hψc
  have hΘc : Continuous Θ := K_cont hs0 hsd hψ.continuous hψc
  have hKi : ∀ i y, fderiv ℝ Θ y (EuclideanSpace.single i (1 : ℝ)) = kernelConvDeriv d s i ψ y :=
    fun i y => convFun_D1 hl hψ1 hψc i y
  have hKc : ∀ i, Continuous (kernelConvDeriv d s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hKb : ∀ i, ∃ C1, ∀ y, |kernelConvDeriv d s i ψ y| ≤ C1 * (1 + ‖y‖) := fun i =>
    conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hv : ∀ i y, |fderiv ℝ (thermalDensity d s a β) y (EuclideanSpace.single i (1 : ℝ))| ≤
      C * Real.exp (-c * ‖y‖ ^ 2) := fun i y => s79g_D1_rho hT i y
  have hper : ∀ i : Fin d,
      Integrable (fun y => Θ y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
        (EuclideanSpace.single i (1 : ℝ))) ∧
      ∫ x, D1 i u x * (thermalDensity d s a β x * kernelConvDeriv d s i ψ x) =
        -∫ y, Θ y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
          (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    obtain ⟨C1, hC1⟩ := hKb i
    have hC10 : 0 ≤ C1 := by
      have := hC1 (0 : Euc d); simp only [norm_zero, add_zero, mul_one] at this
      exact (abs_nonneg _).trans this
    have key := s79g_ibp (K := max (C0 * B1) (max (C0 * B2) (C1 * B1))) hT hΘd
      ((D1_contDiff hu.1 i).differentiable one_ne_zero) hΘc (D1_contDiff hu.1 i).continuous
      (by simp only [hKi]; exact hKc i)
      (HRS.MS.UniqN2b.n2b_D1D1_cont hu.1 i i) (v := EuclideanSpace.single i (1 : ℝ))
      (fun y => by
        rw [abs_mul]
        calc |Θ y| * |D1 i u y| ≤ (C0 * (1 + ‖y‖)) * B1 :=
              mul_le_mul (hC0 y) (hD1u i y) (abs_nonneg _) (by positivity)
          _ = (C0 * B1) * (1 + ‖y‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      (fun y => by
        rw [abs_mul]
        calc |Θ y| * |fderiv ℝ (D1 i u) y (EuclideanSpace.single i (1 : ℝ))|
              ≤ (C0 * (1 + ‖y‖)) * B2 :=
              mul_le_mul (hC0 y) (hB2 i i y) (abs_nonneg _) (by positivity)
          _ = (C0 * B2) * (1 + ‖y‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
              (by positivity))
      (fun y => by
        rw [abs_mul, hKi]
        calc |kernelConvDeriv d s i ψ y| * |D1 i u y| ≤ (C1 * (1 + ‖y‖)) * B1 :=
              mul_le_mul (hC1 y) (hD1u i y) (abs_nonneg _) (by positivity)
          _ = (C1 * B1) * (1 + ‖y‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
              (by positivity))
      (hv i)
    refine ⟨key.1, ?_⟩
    rw [key.2, neg_neg]
    congr 1
    funext y
    rw [hKi]
    ring
  have hsum : ∑ i : Fin d, ∫ y, Θ y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
        (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, Θ y * (-(thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y)) := by
    rw [← integral_finsetSum _ (fun i _ => (hper i).1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← Finset.mul_sum, s79g_div_rho hd hs0 hsd ha hβ hρ hu.1 y]
  rw [Finset.sum_congr rfl fun i _ => (hper i).2, Finset.sum_neg_distrib, hsum, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

end HRS.MS.S79G
