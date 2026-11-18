import HRS.MS.ShiftFldAux10

/-!
# S79P: weak form of the nonlocal term against a test function

`s79g_nlw`: for `u ∈ C_b²`, `ψ ∈ C_c²` (stationary quadratic dynamics, `ρ = thermalDensity`):
`∫ ψ · nlTermRd D ρ u = ∑_i ∫ ∂_i u · (ρ · (∂_i g*ψ))`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.S21 HRS.MH.DualityRd HRS.MS.UniqT3 HRS.MS.UniqNDefs HRS.Whole.AppendixALemmas
open HRS (Euc)

variable {d : ℕ}

theorem s79g_nlw (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, ψ x * nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u x =
      ∑ i : Fin d, ∫ x, D1 i u x * (thermalDensity d s a β x * kernelConvDeriv d s i ψ x) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hreg := s21_regSlice hd hs0 hsd ha hβ
  have hdual := HRS.MS.Fcau.fcau_nonlocal_duality (by omega) (quadraticGradientDyn d s a β)
    (show 0 ≤ (quadraticGradientDyn d s a β).s from hs0) (show (quadraticGradientDyn d s a β).s < d from hsd)
    hreg hu hψ hψc
  rw [hdual.2]
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  obtain ⟨Bu, hBu0, hBu⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 0) (by norm_num)
  obtain ⟨B1, hB10, hB1⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 1) (by norm_num)
  have hub : ∀ x, |u x| ≤ Bu := fun x => by
    have := hBu x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hD1u : ∀ i x, |D1 i u x| ≤ B1 := fun i x =>
    (HRS.MS.UniqN2b.n2b_D1_le i u x).trans (by have := hB1 x; rwa [norm_iteratedFDeriv_one] at this)
  have hu1 : ContDiff ℝ 1 u := hu.1.of_le (by norm_num)
  have hucont : Continuous u := hu1.continuous
  have hD1ucont : ∀ i, Continuous (D1 i u) := fun i =>
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hKc : ∀ i, Continuous (kernelConvDeriv d s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hKb : ∀ i, ∃ C1, ∀ y, |kernelConvDeriv d s i ψ y| ≤ C1 * (1 + ‖y‖) := fun i =>
    conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hKdb : ∀ i, ∃ C1, ∀ y, |D1 i (kernelConvDeriv d s i ψ) y| ≤ C1 * (1 + ‖y‖) := fun i => by
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (HRS.MS.UniqN2b.n2b_D1D1_cont hψ i i)
      (D1_supp (D1_supp hψc i) i)
    refine ⟨C1, fun y => ?_⟩
    rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hψ hψc i i]
    exact hC1 y
  have hKdc : ∀ i, Continuous (D1 i (kernelConvDeriv d s i ψ)) := fun i =>
    HRS.MS.UniqN1c.n1c_D1_kcd_cont hs0 hsd hψ hψc i i
  have hKdiff : ∀ i, Differentiable ℝ (kernelConvDeriv d s i ψ) := fun i =>
    convFun_diff hl (D1_contDiff hψ i) (D1_supp hψc i)
  have hv : ∀ i y, |fderiv ℝ (thermalDensity d s a β) y (EuclideanSpace.single i (1 : ℝ))| ≤
      C * Real.exp (-c * ‖y‖ ^ 2) := fun i y => s79g_D1_rho hT i y
  have hI : ∀ i : Fin d, ∫ x, u x * fderiv ℝ (fun y => thermalDensity d s a β y * kernelConvDeriv d s i ψ y) x
      (EuclideanSpace.single i (1 : ℝ)) =
        -∫ x, D1 i u x * (thermalDensity d s a β x * kernelConvDeriv d s i ψ x) := by
    intro i
    obtain ⟨C1, hC1⟩ := hKb i
    obtain ⟨C2, hC2⟩ := hKdb i
    have hC10 : 0 ≤ C1 := by
      have := hC1 (0 : Euc d); simp only [norm_zero, add_zero, mul_one] at this; exact (abs_nonneg _).trans this
    have hC20 : 0 ≤ C2 := by
      have := hC2 (0 : Euc d); simp only [norm_zero, add_zero, mul_one] at this; exact (abs_nonneg _).trans this
    refine (s79g_ibp (K := max (Bu * C1) (max (Bu * C2) (B1 * C1))) hT (hu1.differentiable one_ne_zero)
      (hKdiff i) hucont (hKc i) ((hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hKdc i) (fun y => ?_) (fun y => ?_) (fun y => ?_) (hv i)).2
    · rw [abs_mul]
      calc |u y| * |kernelConvDeriv d s i ψ y| ≤ Bu * (C1 * (1 + ‖y‖)) :=
            mul_le_mul (hub y) (hC1 y) (abs_nonneg _) hBu0
        _ = (Bu * C1) * (1 + ‖y‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · rw [abs_mul]
      calc |u y| * |fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single i (1 : ℝ))|
            ≤ Bu * (C2 * (1 + ‖y‖)) := mul_le_mul (hub y) (hC2 y) (abs_nonneg _) hBu0
        _ = (Bu * C2) * (1 + ‖y‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
            (by positivity)
    · rw [abs_mul]
      calc |fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))| * |kernelConvDeriv d s i ψ y|
            ≤ B1 * (C1 * (1 + ‖y‖)) := mul_le_mul (hD1u i y) (hC1 y) (abs_nonneg _) hB10
        _ = (B1 * C1) * (1 + ‖y‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
            (by positivity)
  unfold nMain
  have hs' : (quadraticGradientDyn d s a β).s = s := rfl
  simp only [hs']
  have hM : ∀ i j : Fin d, (quadraticGradientDyn d s a β).M j i = if j = i then -1 else 0 := by
    intro i j
    show (-1 : Matrix (Fin d) (Fin d) ℝ) j i = _
    simp only [Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  simp only [hM, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hI i, neg_neg]

end HRS.MS.S79G
