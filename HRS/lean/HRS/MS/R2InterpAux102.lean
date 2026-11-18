import HRS.MS.R2InterpAux101

/-!
# S10.2 (worker S10R), part 102: the filtration frozen at negative times

The Itô formula (`ito_formula`) asks the initial value to be measurable for `ℱ_t` at EVERY real `t`, including negative times, where a filtration produced by
`IsR2Realization.filtered` carries no information.  Freezing the filtration at time `0` for `t ≤ 0` keeps all the filtered-solution properties.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

/-- `ℱ'_t = ℱ_{max(t,0)}`. -/
def s102_shift {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := ℱ (max t 0)
  mono' := fun _ _ h => ℱ.mono (max_le_max h le_rfl)
  le' := fun t => ℱ.le _

theorem s102_shift_apply_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) {t : ℝ} (ht : 0 ≤ t) :
    s102_shift ℱ t = ℱ t := by
  show ℱ (max t 0) = ℱ t
  rw [max_eq_left ht]

theorem s102_shift_neg {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) {t : ℝ} (ht : t ≤ 0) :
    s102_shift ℱ t = s102_shift ℱ 0 := by
  show ℱ (max t 0) = ℱ (max 0 0)
  rw [max_eq_right ht, max_self]

theorem s102_shift_filtered {Ω : Type*} {mΩ : MeasurableSpace Ω} {N d : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hF : IsWholeFilteredSolution P ℱ W' W X) : IsWholeFilteredSolution P (s102_shift ℱ) W' W X := by
  have hnn : ∀ t : ℝ≥0, s102_shift ℱ (t : ℝ) = ℱ t := fun t => s102_shift_apply_nonneg ℱ t.2
  refine ⟨⟨fun t s hs hP0 => hF.brownian.complete _ s hs hP0, fun t => ?_, hF.brownian.zero, hF.brownian.cont,
    fun s t hst => ?_, hF.brownian.gaussian_incr⟩, hF.coords, fun t => ?_, ?_⟩
  · rw [hnn]; exact hF.brownian.adapted t
  · rw [hnn]; exact hF.brownian.indep_incr s t hst
  · rw [hnn]; exact hF.adapted t
  · intro i
    rcases le_or_gt 0 i with hi | hi
    · have := hF.progressive i
      rw [s102_shift_apply_nonneg ℱ hi]
      exact this
    · rw [s102_shift_neg ℱ hi.le]
      have h0 := hF.adapted 0
      have hfun : (fun p : Set.Iic i × Ω => ofNNRealTime X (p.1 : ℝ) p.2) = fun p => X 0 p.2 := by
        funext p
        have : (p.1 : ℝ) ≤ 0 := p.1.2.trans hi.le
        simp [ofNNRealTime, Real.toNNReal_of_nonpos this]
      rw [hfun, s102_shift_apply_nonneg ℱ le_rfl]
      exact @Measurable.comp _ _ _ (Subtype.instMeasurableSpace.prod (ℱ 0)) (ℱ 0) _ _ _ h0
        (@measurable_snd _ _ Subtype.instMeasurableSpace (ℱ 0))

end HRS.MS.R2Interp

end
