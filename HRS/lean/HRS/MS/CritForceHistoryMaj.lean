import HRS.MS.CritForceHistory

/-!
# S8.2.06 (majorant form): the uniform-history estimate without measurability of the suprema

`s82_history_bound` asks that the recent and old block suprema be `AEMeasurable` (in order to apply the
geometric summation to them).  Measurability of an uncountable supremum needs continuity in the
observed time, which is extra work in the scalar core.  Here the hypothesis is weakened to the
existence of AEMeasurable `ℝ≥0∞`-valued almost sure majorants with the same `L²` bounds (the
suprema themselves are admissible majorants, so `s82_history_bound` is a special case); the conclusion
is the same.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

theorem s82_history_bound_maj {ι Ω : Type} [Countable ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ι → ℝ → ℝ → Ω → ℝ) (w : ι → ℝ) (C q ε T a₀ : ℝ)
    (hC : 0 ≤ C) (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 ≤ ε)
    (ha₀ : 0 ≤ a₀)
    (hw : ∀ i, 0 ≤ w i) (hws : Summable (fun i => (w i) ^ 2))
    (hF : ∀ᵐ ζ ∂P, ∀ i, ∀ t : Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => F i (a₀ + t) r ζ) (Set.Icc 0 (a₀ + t)))
    (hblocks : ∀ i, ∃ R : Ω → ℝ≥0∞, AEMeasurable R P ∧
      (∀ᵐ ζ ∂P, s82RecentSup F T a₀ i ζ ≤ R ζ) ∧
      (∫⁻ ζ, (R ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (C * w i * ε) ∧
      ∀ j : ℕ, ∃ A : Ω → ℝ≥0∞, AEMeasurable A P ∧
        (∀ᵐ ζ ∂P, s82PastSup F T a₀ j i ζ ≤ A ζ) ∧
        (∫⁻ ζ, (A ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (C * w i * ε * q ^ j)) :
    (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T,
      l2NormE (fun i => ∫ r in Set.Icc (0 : ℝ) (a₀ + t),
        F i (a₀ + t) r ζ)) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (s82HistoryConstant C q w * ε) := by
  choose R hRm hRle hRb hAj using hblocks
  choose A hAm hAle hAb using hAj
  have hEnv : ∀ i, AEMeasurable (fun ζ => R i ζ + ∑' j : ℕ, A i j ζ) P ∧
      (∫⁻ ζ, (R i ζ + ∑' j : ℕ, A i j ζ) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((C * ε * (1 + (1 - q)⁻¹)) * w i) := by
    intro i
    have h := s82_geometric_L2 P (R i) (A i) (C * w i * ε) q
      (by have := hw i; positivity) hq0 hq1 (hRm i) (hAm i) (hRb i) (hAb i)
    refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))⟩
    ring
  have hRae : ∀ᵐ ζ ∂P, ∀ i, s82RecentSup F T a₀ i ζ ≤ R i ζ := ae_all_iff.2 hRle
  have hAae : ∀ᵐ ζ ∂P, ∀ i j, s82PastSup F T a₀ j i ζ ≤ A i j ζ :=
    ae_all_iff.2 fun i => ae_all_iff.2 (hAle i)
  have hB : 0 ≤ C * ε * (1 + (1 - q)⁻¹) :=
    mul_nonneg (mul_nonneg hC hε) (by have : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
                                      linarith)
  have hZA : ∀ᵐ ζ ∂P, ∀ t : Set.Icc (0 : ℝ) T, ∀ i,
      ENNReal.ofReal |(fun (s : ℝ) (i : ι) (ζ : Ω) =>
        ∫ r in Set.Icc (0 : ℝ) (a₀ + s), F i (a₀ + s) r ζ) t i ζ| ≤
        R i ζ + ∑' j : ℕ, A i j ζ := by
    filter_upwards [hF, hRae, hAae] with ζ hζ hR hA t i
    have h := s82_partition_abs_le (fun r => F i (a₀ + t) r ζ) a₀ t ha₀ t.property.1 (hζ i t)
    refine h.trans (add_le_add ?_ (ENNReal.tsum_le_tsum fun j => ?_))
    · exact (le_iSup (fun t : Set.Icc (0 : ℝ) T =>
        ENNReal.ofReal |s82Recent F a₀ t i ζ|) t).trans (hR i)
    · exact (le_iSup (fun t : Set.Icc (0 : ℝ) T =>
        ENNReal.ofReal |s82Past F a₀ j t i ζ|) t).trans (hA i j)
  have h3 := s82_coordinate_L2 P T
    (fun (s : ℝ) (i : ι) (ζ : Ω) => ∫ r in Set.Icc (0 : ℝ) (a₀ + s), F i (a₀ + s) r ζ)
    (fun i ζ => R i ζ + ∑' j : ℕ, A i j ζ) w
    (C * ε * (1 + (1 - q)⁻¹)) hB hw hws
    (fun i => (hEnv i).1) (fun i => (hEnv i).2) hZA
  refine h3.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold s82HistoryConstant
  ring

end HRS.MS.S82BD
