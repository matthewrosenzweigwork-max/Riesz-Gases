import HRS.MS.ShiftFldAux16

/-!
# S79P: Green's formula for the weighted operator `𝒜` and centering
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_memcb_bounds {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) :
    ∃ B0 B1 B2 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧ (∀ x, |u x| ≤ B0) ∧ (∀ i x, |D1 i u x| ≤ B1) ∧
      (∀ i j x, |D1 j (D1 i u) x| ≤ B2) := by
  obtain ⟨Bu, hBu0, hBu⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 0) (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 1) (by norm_num)
  obtain ⟨B2, hB20, hB2⟩ := s79g_D1D1_bound hu
  refine ⟨Bu, B1, B2, hBu0, hB10, hB20, fun x => ?_, fun i x => ?_, hB2⟩
  · have := hBu x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · exact (HRS.MS.UniqN2b.n2b_D1_le i u x).trans (by have := hB1 x; rwa [norm_iteratedFDeriv_one] at this)

theorem s79g_lin_of_le {x K : ℝ} (hx : |x| ≤ K) (y : Euc d) : |x| ≤ K * (1 + ‖y‖) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hx
  have := norm_nonneg y
  nlinarith

theorem s79g_green (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u g : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hg : HRS.MemCb 2 g) :
    ∫ x, g x * (thermalDensity d s a β x * Aop d s a β (thermalDensity d s a β) u x) =
      ∑ i : Fin d, ∫ x, D1 i g x * (thermalDensity d s a β x * D1 i u x) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨u0, u1, u2, hu0, hu1, hu2, hbu0, hbu1, hbu2⟩ := s79g_memcb_bounds hu
  obtain ⟨g0, g1, g2, hg0, hg1, hg2, hbg0, hbg1, hbg2⟩ := s79g_memcb_bounds hg
  have hv : ∀ i y, |fderiv ℝ (thermalDensity d s a β) y (EuclideanSpace.single i (1 : ℝ))| ≤
      C * Real.exp (-c * ‖y‖ ^ 2) := fun i y => s79g_D1_rho hT i y
  have hper : ∀ i : Fin d,
      Integrable (fun y => g y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
        (EuclideanSpace.single i (1 : ℝ))) ∧
      ∫ y, g y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
          (EuclideanSpace.single i (1 : ℝ)) =
        -∫ x, D1 i g x * (thermalDensity d s a β x * D1 i u x) := by
    intro i
    exact s79g_ibp (K := g0 * u1 + g0 * u2 + g1 * u1) hT (hg.1.differentiable (by norm_num))
      ((D1_contDiff hu.1 i).differentiable one_ne_zero) hg.1.continuous (D1_contDiff hu.1 i).continuous
      ((hg.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (HRS.MS.UniqN2b.n2b_D1D1_cont hu.1 i i) (v := EuclideanSpace.single i (1 : ℝ))
      (fun y => by
        exact s79g_lin_of_le (K := g0 * u1 + g0 * u2 + g1 * u1) ((abs_mul _ _).le.trans (mul_le_mul (hbg0 y) (hbu1 i y) (abs_nonneg _) hg0 |>.trans
          (by nlinarith [mul_nonneg hg0 hu2, mul_nonneg hg1 hu1]))) y)
      (fun y => by
        exact s79g_lin_of_le (K := g0 * u1 + g0 * u2 + g1 * u1) ((abs_mul _ _).le.trans (mul_le_mul (hbg0 y) (hbu2 i i y) (abs_nonneg _) hg0 |>.trans
          (by nlinarith [mul_nonneg hg0 hu1, mul_nonneg hg1 hu1]))) y)
      (fun y => by
        exact s79g_lin_of_le (K := g0 * u1 + g0 * u2 + g1 * u1) ((abs_mul _ _).le.trans (mul_le_mul (hbg1 i y) (hbu1 i y) (abs_nonneg _) hg1 |>.trans
          (by nlinarith [mul_nonneg hg0 hu1, mul_nonneg hg0 hu2]))) y)
      (hv i)
  have hsum : ∑ i : Fin d, ∫ y, g y * fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
        (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, g y * (-(thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y)) := by
    rw [← integral_finsetSum _ (fun i _ => (hper i).1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← Finset.mul_sum, s79g_div_rho hd hs0 hsd ha hβ hρ hu.1 y]
  rw [Finset.sum_congr rfl fun i _ => (hper i).2, Finset.sum_neg_distrib] at hsum
  rw [← neg_neg (∑ i : Fin d, ∫ x, D1 i g x * (thermalDensity d s a β x * D1 i u x)), hsum,
    ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

end HRS.MS.S79G
