import HRS.MS.S113X2A1b

/-!
# S11.3 X2 part A1c: the exit time from an open set is a stopping time for the particle solution
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- The exit time `τ` from an open set `D`, a stopping time of the (complete) filtration; a.s. the
survival event up to time `t` is `{t < τ}`, and a finite exit time is a non-negative time at which the path is
outside `D`. -/
theorem s113a_exit_data {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → EucConfig d N}
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i)
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) :
    ∃ τ : Ω → WithTop ℝ, IsStoppingTime ℱ τ ∧ ∀ᵐ ζ ∂P,
      (∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ) ∧
      ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → 0 ≤ c ∧ X c.toNNReal ζ ∉ D := by
  classical
  obtain ⟨Nn, hNm, hN0, hNc⟩ : ∃ Nn : Set Ω, MeasurableSet Nn ∧ P Nn = 0 ∧
      ∀ ζ ∉ Nn, ∀ i, Continuous fun t => X t ζ i := by
    refine ⟨toMeasurable P {ζ | ¬ ∀ i, Continuous fun t => X t ζ i}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]; exact ae_iff.1 hcont
    · intro ζ hζ; by_contra hc; exact hζ (subset_toMeasurable _ _ hc)
  have hN : ∀ t, MeasurableSet[ℱ t] Nn := fun t => hF.brownian.complete t Nn hNm hN0
  let Y : ℝ → Ω → EucConfig d N := fun t ζ => if ζ ∈ Nn then 0 else X (Real.toNNReal t) ζ
  have hYad : Adapted ℱ Y := fun t =>
    Measurable.ite (m := ℱ t) (hN t) measurable_const (hF.progressive.adapted t)
  have hYc : ∀ ζ, Continuous fun t => Y t ζ := by
    intro ζ
    by_cases h : ζ ∈ Nn
    · simp only [Y, h, ite_true]; exact continuous_const
    · simp only [Y, h, ite_false]
      exact (continuous_pi (hNc ζ h)).comp continuous_real_toNNReal
  refine ⟨exitTime Y D 0, isStoppingTime_exitTime ℱ Y hYad hYc hD 0, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ζ hζ
  have hY : ∀ t : ℝ, Y t ζ = X (Real.toNNReal t) ζ := fun t => by simp [Y, hζ]
  refine ⟨fun t => ⟨fun hs => ?_, fun hlt r hr => ?_⟩, fun c hc => ?_⟩
  · by_contra hnot
    rw [not_lt] at hnot
    cases hτ : exitTime Y D 0 ζ with
    | top => rw [hτ] at hnot; exact absurd hnot (by simp)
    | coe c =>
      rw [hτ] at hnot
      have hcl : c ≤ (t : ℝ) := by exact_mod_cast hnot
      have h0 : (0 : WithTop ℝ) ≤ exitTime Y D 0 ζ := le_hittingAfter ζ
      rw [hτ] at h0
      have h0' : (0 : ℝ) ≤ c := by exact_mod_cast h0
      have hout := notMem_of_exitTime_eq Y D hD 0 ζ (hYc ζ) c hτ
      rw [hY] at hout
      refine hout (hs (Real.toNNReal c) ?_)
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0']
      exact hcl
  · have := mem_of_lt_exitTime Y D 0 ζ (r : ℝ) r.2 (lt_of_le_of_lt (by exact_mod_cast hr) hlt)
    rw [hY] at this
    simpa using this
  · have h0 : (0 : WithTop ℝ) ≤ exitTime Y D 0 ζ := le_hittingAfter ζ
    rw [hc] at h0
    have h0' : (0 : ℝ) ≤ c := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have hout := notMem_of_exitTime_eq Y D hD 0 ζ (hYc ζ) c hc
    rwa [hY] at hout

end HRS.MS.S113X2

end
