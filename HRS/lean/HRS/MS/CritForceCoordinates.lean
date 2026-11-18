import HRS.MS.CritForceDefs

/-!
# S8.2.03: countable coordinate squares after the observed-time supremum
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

lemma s82_sqrt_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma s82_le_of_sqrt_le {x y : ℝ≥0∞} (h : x ^ (1 / 2 : ℝ) ≤ y) : x ≤ y ^ 2 := by
  calc x = (x ^ (1 / 2 : ℝ)) ^ 2 := (s82_sqrt_sq x).symm
    _ ≤ y ^ 2 := pow_le_pow_left' h 2

theorem s82_coordinate_L2 {ι Ω : Type} [Countable ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (Z : ℝ → ι → Ω → ℝ) (A : ι → Ω → ℝ≥0∞) (b : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i, 0 ≤ b i)
    (hbs : Summable (fun i => (b i) ^ 2))
    (hAm : ∀ i, AEMeasurable (A i) P)
    (hA : ∀ i, (∫⁻ ζ, (A i ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * b i))
    (hZA : ∀ᵐ ζ ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
      ENNReal.ofReal |Z t i ζ| ≤ A i ζ) :
    (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T,
      l2NormE (fun i => Z t i ζ)) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B * Real.sqrt (∑' i, (b i) ^ 2)) := by
  -- pointwise bound by the countable sum of squares
  have hpt : ∀ᵐ ζ ∂P, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ^ 2 ≤
      ∑' i, (A i ζ) ^ 2 := by
    filter_upwards [hZA] with ζ hζ
    have h1 : (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ≤
        (∑' i, (A i ζ) ^ 2) ^ (1 / 2 : ℝ) := by
      refine iSup_le fun t => ?_
      unfold l2NormE
      refine ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun i => ?_) (by norm_num)
      calc ENNReal.ofReal (Z t i ζ ^ 2) = (ENNReal.ofReal |Z t i ζ|) ^ 2 := by
            rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
        _ ≤ (A i ζ) ^ 2 := pow_le_pow_left' (hζ t i) 2
    calc (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ^ 2
        ≤ ((∑' i, (A i ζ) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' h1 2
      _ = ∑' i, (A i ζ) ^ 2 := s82_sqrt_sq _
  -- integrate
  have hint : ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ^ 2 ∂P ≤
      ∑' i, ENNReal.ofReal (B ^ 2 * (b i) ^ 2) := by
    calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ^ 2 ∂P
        ≤ ∫⁻ ζ, ∑' i, (A i ζ) ^ 2 ∂P := lintegral_mono_ae hpt
      _ = ∑' i, ∫⁻ ζ, (A i ζ) ^ 2 ∂P := lintegral_tsum fun i => (hAm i).pow_const 2
      _ ≤ ∑' i, ENNReal.ofReal (B ^ 2 * (b i) ^ 2) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          have h := s82_le_of_sqrt_le (hA i)
          calc _ ≤ (ENNReal.ofReal (B * b i)) ^ 2 := h
            _ = ENNReal.ofReal (B ^ 2 * (b i) ^ 2) := by
                rw [← ENNReal.ofReal_pow (mul_nonneg hB (hb i))]
                congr 1; ring
  have hsum : ∑' i, ENNReal.ofReal (B ^ 2 * (b i) ^ 2) =
      ENNReal.ofReal (B ^ 2 * ∑' i, (b i) ^ 2) := by
    rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
      (hbs.mul_left _)]
  have hS : 0 ≤ ∑' i, (b i) ^ 2 := tsum_nonneg fun i => by positivity
  have hfin : ENNReal.ofReal (B ^ 2 * ∑' i, (b i) ^ 2) =
      (ENNReal.ofReal (B * Real.sqrt (∑' i, (b i) ^ 2))) ^ 2 := by
    rw [← ENNReal.ofReal_pow (mul_nonneg hB (Real.sqrt_nonneg _))]
    congr 1
    rw [mul_pow, Real.sq_sqrt hS]
  calc (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun i => Z t i ζ)) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal (B * Real.sqrt (∑' i, (b i) ^ 2))) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hint.trans (hsum.trans hfin).le) (by norm_num)
    _ = ENNReal.ofReal (B * Real.sqrt (∑' i, (b i) ^ 2)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

end HRS.MS.S82BD
