import Mathlib

/-!
# S11.3.R1 (breakdown packet R1): measurable Lebesgue-density ratio and the finite Radon-Nikodym representative
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S113BD

variable {α : Type*} [MeasurableSpace α]

theorem s113_raw_density_ratio (lam : Measure α) [SFinite lam]
    (q f : α → ℝ) (hq : Measurable q) (hf : Measurable f)
    (hq0 : ∀ x, 0 ≤ q x) (hf0 : ∀ x, 0 ≤ f x)
    (hqpos : ∀ᵐ x ∂lam, 0 < q x)
    (hiq : Integrable q lam) (hif : Integrable f lam) :
    Measurable (fun x => f x / q x) ∧
      lam.withDensity (fun x => ENNReal.ofReal (f x)) ≪
        lam.withDensity (fun x => ENNReal.ofReal (q x)) ∧
      ∀ᵐ x ∂(lam.withDensity (fun y => ENNReal.ofReal (q y))),
        ((lam.withDensity (fun y => ENNReal.ofReal (f y))).rnDeriv
          (lam.withDensity (fun y => ENNReal.ofReal (q y))) x).toReal = f x / q x := by
  have hqm : Measurable fun x => ENNReal.ofReal (q x) := ENNReal.measurable_ofReal.comp hq
  have hgm : Measurable fun x => ENNReal.ofReal (f x / q x) :=
    ENNReal.measurable_ofReal.comp (hf.div hq)
  have hfin : IsFiniteMeasure (lam.withDensity (fun x => ENNReal.ofReal (q x))) :=
    isFiniteMeasure_withDensity_ofReal hiq.2
  have hrep : lam.withDensity (fun x => ENNReal.ofReal (f x)) =
      (lam.withDensity (fun x => ENNReal.ofReal (q x))).withDensity (fun x => ENNReal.ofReal (f x / q x)) := by
    rw [← withDensity_mul lam hqm hgm]
    refine withDensity_congr_ae ?_
    filter_upwards [hqpos] with x hx
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hq0 x), mul_div_cancel₀ _ hx.ne']
  refine ⟨hf.div hq, ?_, ?_⟩
  · rw [hrep]; exact withDensity_absolutelyContinuous _ _
  · have h := Measure.rnDeriv_withDensity (lam.withDensity (fun x => ENNReal.ofReal (q x))) hgm
    rw [← hrep] at h
    filter_upwards [h] with x hx
    rw [hx, ENNReal.toReal_ofReal (div_nonneg (hf0 x) (hq0 x))]

end HRS.MS.S113BD
