import HRS.MS.MovEntAux19

/-!
# S6.6, packet P5 (part 3): time-averaged bounds for a progressive configuration process

* `s66_swap_bound`: `E ∫_a^b G(X_s) ds ≤ (b-a) c` if `E G(X_s) ≤ c` for each `s ∈ [a,b]` (Tonelli with the clamped process).
* `s66_le_one_add_sq`: `x ≤ 1 + x²` in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

variable {d : ℕ}

theorem s66_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  by_cases h : x ≤ 1
  · exact h.trans le_self_add
  · push Not at h
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := mul_le_mul' le_rfl h.le
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

theorem s66_swap_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {N : ℕ} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsProgressive ℱ (ofNNRealTime X)) (G : EucConfig d N → ℝ≥0∞) (hG : Measurable G) (a b : ℝ)
    (c : ℝ≥0∞) (hc : ∀ s ∈ Set.Icc a b, ∫⁻ ω, G (X s.toNNReal ω) ∂P ≤ c) :
    ∫⁻ ω, (∫⁻ s in Set.Icc a b, G (X s.toNNReal ω)) ∂P ≤ ENNReal.ofReal (b - a) * c := by
  have e1 : ∀ ω, ∫⁻ s in Set.Icc a b, G (X s.toNNReal ω) =
      ∫⁻ s in Set.Icc a b, G (ofNNRealTime X (min s b) ω) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp [ofNNRealTime, min_eq_left hs.2]
  simp_rw [e1]
  have hmeas : Measurable (fun p : ℝ × Ω => G (ofNNRealTime X (min p.1 b) p.2)) :=
    hG.comp (HRS.measurable_clamp hX b)
  have hmeas' : Measurable (fun p : Ω × ℝ => G (ofNNRealTime X (min p.2 b) p.1)) :=
    hmeas.comp measurable_swap
  rw [lintegral_lintegral_swap hmeas'.aemeasurable]
  calc ∫⁻ s in Set.Icc a b, ∫⁻ ω, G (ofNNRealTime X (min s b) ω) ∂P
      ≤ ∫⁻ s in Set.Icc a b, c := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        have : ofNNRealTime X (min s b) = fun ω => X s.toNNReal ω := by
          funext ω; simp [ofNNRealTime, min_eq_left hs.2]
        rw [this]
        exact hc s hs
    _ = ENNReal.ofReal (b - a) * c := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]

theorem s66_lintegral_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {N : ℕ}
    {X : ℝ≥0 → Ω → EucConfig d N} (hX : IsProgressive ℱ (ofNNRealTime X)) (G : EucConfig d N → ℝ≥0∞)
    (hG : Measurable G) (a b : ℝ) :
    Measurable (fun ω => ∫⁻ s in Set.Icc a b, G (X s.toNNReal ω)) := by
  have e1 : ∀ ω, ∫⁻ s in Set.Icc a b, G (X s.toNNReal ω) =
      ∫⁻ s in Set.Icc a b, G (ofNNRealTime X (min s b) ω) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp [ofNNRealTime, min_eq_left hs.2]
  simp_rw [e1]
  have hmeas : Measurable (fun p : ℝ × Ω => G (ofNNRealTime X (min p.1 b) p.2)) :=
    hG.comp (HRS.measurable_clamp hX b)
  exact (hmeas.comp (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc a b))

end HRS.MS.MovEnt

end
