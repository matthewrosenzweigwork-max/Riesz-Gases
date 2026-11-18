import HRS.Prob.HilbertMartingale

/-!
# EQ-TRACE, Minkowski for series in `L²`

For measurable `f_i : Ω → ℝ≥0∞` with `∫⁻ f_i² ≤ a_i²`: `∫⁻ (∑_i f_i)² ≤ (∑_i a_i)²` (countable index).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQTrace

theorem eqtrace_mink {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} [Countable ι]
    (f : ι → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (a : ι → ℝ≥0∞)
    (ha : ∀ i, ∫⁻ ω, f i ω ^ 2 ∂P ≤ a i ^ 2) :
    ∫⁻ ω, (∑' i, f i ω) ^ 2 ∂P ≤ (∑' i, a i) ^ 2 := by
  have hcs : ∀ i j, ∫⁻ ω, f i ω * f j ω ∂P ≤ a i * a j := by
    intro i j
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
      (hf i).aemeasurable (hf j).aemeasurable
    refine h.trans ?_
    have e : ∀ k, (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ a k := by
      intro k
      have h1 : ∫⁻ ω, f k ω ^ (2 : ℝ) ∂P ≤ a k ^ 2 := by
        simpa [ENNReal.rpow_two] using ha k
      calc (∫⁻ ω, f k ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ (a k ^ 2) ^ (1 / (2 : ℝ)) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = a k := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    exact mul_le_mul' (e i) (e j)
  have hexp : ∀ ω, (∑' i, f i ω) ^ 2 = ∑' i, ∑' j, f i ω * f j ω := by
    intro ω
    rw [sq, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun i => by rw [← ENNReal.tsum_mul_left]
  simp_rw [hexp]
  rw [lintegral_tsum]
  · calc ∑' i, ∫⁻ ω, ∑' j, f i ω * f j ω ∂P = ∑' i, ∑' j, ∫⁻ ω, f i ω * f j ω ∂P := by
          refine tsum_congr fun i => ?_
          rw [lintegral_tsum]
          exact fun j => ((hf i).mul (hf j)).aemeasurable
      _ ≤ ∑' i, ∑' j, a i * a j := ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => hcs i j
      _ = (∑' i, a i) ^ 2 := by
          rw [sq, ← ENNReal.tsum_mul_right]
          exact tsum_congr fun i => by rw [← ENNReal.tsum_mul_left]
  · intro i
    exact (Measurable.ennreal_tsum fun j => (hf i).mul (hf j)).aemeasurable

end HRS.MD.EQTrace
