import HRS.MS.R2InterpAux85
import HRS.MS.WsStatAux14

/-!
# S10.2 (worker S10R), part 86 (packet F5f): the exact centring of a bounded test along the particle path
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_pairEmp_meas {N : ℕ} (hN : 0 < N) {g : Euc d → ℝ} (hg : Measurable g) :
    Measurable fun Y : EucConfig d N => HRS.Whole.pair (HRS.Whole.empirical Y) g := by
  simp_rw [HRS.Whole.pair_empirical hN]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i))

theorem s102_pairEmp_int {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → EucConfig d N} (hY : Measurable Y) {g : Euc d → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) : Integrable (fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) g) P := by
  refine Integrable.of_bound ((s102_pairEmp_meas hN hg).comp hY).aestronglyMeasurable B
    (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, HRS.Whole.pair_empirical hN, abs_mul, abs_of_nonneg (by positivity)]
  have hs : |∑ i, g (Y ζ i)| ≤ N * B := by
    calc |∑ i, g (Y ζ i)| ≤ ∑ i, |g (Y ζ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
      _ = N * B := by simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ)⁻¹ * |∑ i, g (Y ζ i)| ≤ (N : ℝ)⁻¹ * (N * B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = B := by field_simp

/-- `ζ_N^τ(g) = √N (a_τ - E a_τ)` with `a_τ = μ_N^τ(g) - μ(g)`, for a bounded measurable test `g`. -/
theorem s102_zf_eq {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (τ : ℝ) (hXτ : Measurable (X τ.toNNReal)) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] {g : Euc d → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (ζ : Ω) :
    s102_zf P X ζ τ g = Real.sqrt N * ((HRS.Whole.pair (HRS.Whole.empirical (X τ.toNNReal ζ)) g -
        HRS.Whole.pair μ g) - ∫ ζ', (HRS.Whole.pair (HRS.Whole.empirical (X τ.toNNReal ζ')) g -
        HRS.Whole.pair μ g) ∂P) := by
  have : IsProbabilityMeasure (P.map (X τ.toNNReal)) := ⟨by rw [Measure.map_apply hXτ MeasurableSet.univ]; simp⟩
  have h1 := HRS.MS.S21.s21_E_pair_emp (Nat.succ_le_of_lt hN) P (X τ.toNNReal) hXτ (P.map (X τ.toNNReal)) rfl hg hB
  have h2 : ∫ ζ', (HRS.Whole.pair (HRS.Whole.empirical (X τ.toNNReal ζ')) g - HRS.Whole.pair μ g) ∂P =
      HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X τ.toNNReal))) g - HRS.Whole.pair μ g := by
    rw [integral_sub (s102_pairEmp_int hN hXτ hg hB) (integrable_const _), h1]
    simp
  rw [h2]
  unfold s102_zf
  congr 1
  ring

end HRS.MS.R2Interp

end
