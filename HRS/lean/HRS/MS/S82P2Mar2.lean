import HRS.MS.S82P2Mar1

/-!
# S8.2 (S82P2): bounded density of pinned one-site marginals
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_rn_le {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d) (i : Fin n)
    (hprob : IsProbabilityMeasure
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins)) :
    ∀ᵐ z ∂HRS.Whole.withDensityReal rho,
      ((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
          (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z ≤
        ENNReal.ofReal (1 + 2 * C1) := by
  have hC1 := s82p2_pinCmp_nonneg hP
  haveI : IsProbabilityMeasure ((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
      (fun X => X i)) := ⟨by rw [Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]; simp⟩
  filter_upwards [s82p2_rn_dev hP hN hp hnp hNn pins i,
    Measure.rnDeriv_lt_top ((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
      (fun X => X i)) (HRS.Whole.withDensityReal rho)] with z h1 h2
  rw [← ENNReal.ofReal_toReal h2.ne]
  apply ENNReal.ofReal_le_ofReal
  have hδ := s82p2_deltaN_le_one (N := N) (by omega)
  have hm : min 1 ((1 + ∑ j, q (z - pins j)) / (N : ℝ)) ≤ 1 := min_le_left _ _
  have e1 := abs_le.1 h1
  nlinarith [mul_le_mul_of_nonneg_left hδ hC1, mul_le_mul_of_nonneg_left hm hC1]

lemma s82p2_marg_lintegral_le {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d) (i : Fin n)
    (hprob : IsProbabilityMeasure
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins))
    (H : Euc d → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ z, H z ∂((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
        (fun X => X i)) ≤
      ENNReal.ofReal (1 + 2 * C1) * ∫⁻ z, H z ∂HRS.Whole.withDensityReal rho := by
  rw [s82p2_marg_lintegral _ _ _ _ _ _ _ H hH, ← lintegral_const_mul _ hH]
  exact lintegral_mono_ae ((s82p2_rn_le hP hN hp hnp hNn pins i hprob).mono fun z hz =>
    by gcongr)

end HRS.MS.S82P2
