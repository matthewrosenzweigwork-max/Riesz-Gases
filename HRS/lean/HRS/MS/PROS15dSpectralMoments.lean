import HRS.MS.S21H2_S15c
import HRS.MS.S21G2_S11aB

/-!
# R26-T3.S15d: finite spectral-coordinate second moments of the Gaussian tilt

This is a supporting lemma only. It converts the exact tilted finite-coordinate
product-Gaussian law supplied by S15c into a second-moment identity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_pi_gaussian_coord_second
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) P)
    (v : Fin n → ℝ≥0)
    (hLaw : P.map (fun ω i => X i ω) = Measure.pi (fun i => gaussianReal 0 (v i)))
    (i : Fin n) :
    ∫ ω, X i ω ^ 2 ∂P = v i := by
  have hvec : AEMeasurable (fun ω (j : Fin n) => X j ω) P :=
    AEMeasurable.of_eval hX
  have hmap := AEMeasurable.map_map_of_aemeasurable
    (measurable_pi_apply i).aemeasurable hvec
  have hcoord : P.map (X i) = gaussianReal 0 (v i) := by
    calc
      P.map (X i) =
        (P.map (fun ω (j : Fin n) => X j ω)).map (fun z : Fin n → ℝ => z i) := by
          simpa [Function.comp_def] using hmap.symm
      _ = _ := by
        rw [hLaw, show (fun z : Fin n → ℝ => z i) = Function.eval i from rfl,
          Measure.pi_map_eval]
        simp
  exact s21g2_s11a_second (hX i) hcoord

end HRS.MS.R26T3
