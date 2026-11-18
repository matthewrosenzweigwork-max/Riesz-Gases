import HRS.MS.S113PowerAux2

/-!
# S11.3.E3 (breakdown packet E3): entropy bound for the moving-reference source under the power tilt
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

section Entropy

variable {α : Type*} [MeasurableSpace α]

theorem s113_power_source_bound (Q : Measure α) [IsProbabilityMeasure Q]
    (r R : α → ℝ) (hr : Measurable r) (hR : Measurable R)
    (hr0 : ∀ x, 0 ≤ r x) (p B cL C L : ℝ)
    (hp : 1 < p) (hB : ∀ x, r x ≤ B)
    (hM : 0 < s113_powerMass Q r p)
    (hcL : 0 < cL) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hzero : L = 0 → ∀ x, R x = 0)
    (hexp : 0 < L →
      ∫⁻ x, ENNReal.ofReal (Real.exp ((cL / L) * |R x|)) ∂Q ≤
        ENNReal.ofReal (Real.exp C)) :
    Integrable R (s113_powerTilt Q r p) ∧
      ∫ x, R x ∂(s113_powerTilt Q r p) ≤
        (L / cL) * (p * (∫ x, Real.log (r x) ∂(s113_powerTilt Q r p)) -
          Real.log (s113_powerMass Q r p) + C) := by
  obtain ⟨hprob, hac, hkl, hlogint, hklval⟩ := s113_power_entropy Q r hr hr0 p B hp hB hM
  rcases hL.eq_or_lt with h0 | hLpos
  · have hR0 : R = fun _ => 0 := funext (hzero h0.symm)
    subst hR0
    rw [← h0]
    simp
  · have hcL' : 0 < cL / L := div_pos hcL hLpos
    obtain ⟨hi, hbd⟩ := HRS.MS.Wr.wr9_dv_abs Q (s113_powerTilt Q r p) hkl hR hcL' hC (hexp hLpos)
    have hRint : Integrable R (s113_powerTilt Q r p) := by
      refine Integrable.mono' hi hR.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      simp
    refine ⟨hRint, ?_⟩
    calc ∫ x, R x ∂(s113_powerTilt Q r p) ≤ ∫ x, |R x| ∂(s113_powerTilt Q r p) :=
          integral_mono hRint hi (fun x => le_abs_self _)
      _ ≤ (cL / L)⁻¹ * ((InformationTheory.klDiv (s113_powerTilt Q r p) Q).toReal + C) := hbd
      _ = _ := by rw [hklval, inv_div]

end Entropy

end HRS.MS.S113BD
