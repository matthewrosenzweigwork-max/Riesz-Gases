import HRS.MS.Fp81S21WindowSup51

/-! Two-integral sixth-moment majorant for the drift assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- Two jointly measurable nonnegative families with uniform sixth-root
bounds give a sixth-root bound for any pointwise dominated observable. -/
theorem fp81s21_two_lintegral_majorant_six_ae
    {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [SFinite ν] (ξ : Measure U) [SFinite ξ]
    (q : S → Ω → ℝ≥0∞) (k : U → Ω → ℝ≥0∞)
    (hq : Measurable (Function.uncurry q)) (hk : Measurable (Function.uncurry k))
    (K : ℝ≥0∞)
    (hqBound : ∀ s, (∫⁻ ω, q s ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ K)
    (hkBound : ∀ u, (∫⁻ ω, k u ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ K)
    (R : Ω → ℝ≥0∞) (hDom : ∀ᵐ ω ∂P, R ω ≤
      (∫⁻ s, q s ω ∂ν) + ∫⁻ u, k u ω ∂ξ) :
    (∫⁻ ω, R ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤
      ν Set.univ * K + ξ Set.univ * K := by
  let Q : Ω → ℝ≥0∞ := fun ω => ∫⁻ s, q s ω ∂ν
  let J : Ω → ℝ≥0∞ := fun ω => ∫⁻ u, k u ω ∂ξ
  have hQ : Measurable Q := (hq.comp measurable_swap).lintegral_prod_right'
  have hJ : Measurable J := (hk.comp measurable_swap).lintegral_prod_right'
  have hQbound : (∫⁻ ω, Q ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ ν Set.univ * K := by
    have h := fp81s21_lintegral_minkowski_six P ν q hq
    calc
      _ = (∫⁻ ω, Q ω ^ (6 : ℕ) ∂P) ^ (1 / 6 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro ω
        exact ENNReal.rpow_natCast (Q ω) 6
      _ ≤ ∫⁻ s, (∫⁻ ω, q s ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂ν := h
      _ ≤ ∫⁻ _s, K ∂ν := lintegral_mono hqBound
      _ = ν Set.univ * K := by rw [lintegral_const, mul_comm]
  have hJbound : (∫⁻ ω, J ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ≤ ξ Set.univ * K := by
    have h := fp81s21_lintegral_minkowski_six P ξ k hk
    calc
      _ = (∫⁻ ω, J ω ^ (6 : ℕ) ∂P) ^ (1 / 6 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro ω
        exact ENNReal.rpow_natCast (J ω) 6
      _ ≤ ∫⁻ u, (∫⁻ ω, k u ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) ∂ξ := h
      _ ≤ ∫⁻ _u, K ∂ξ := lintegral_mono hkBound
      _ = ξ Set.univ * K := by rw [lintegral_const, mul_comm]
  calc
    _ ≤ (∫⁻ ω, (Q ω + J ω) ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply lintegral_mono_ae
      filter_upwards [hDom] with ω hω
      exact ENNReal.rpow_le_rpow hω (by norm_num)
    _ ≤ (∫⁻ ω, Q ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) +
        (∫⁻ ω, J ω ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) :=
      ENNReal.lintegral_Lp_add_le hQ.aemeasurable hJ.aemeasurable (by norm_num)
    _ ≤ ν Set.univ * K + ξ Set.univ * K := add_le_add hQbound hJbound

#print axioms fp81s21_two_lintegral_majorant_six_ae
end HRS.Fp81.S21
end
