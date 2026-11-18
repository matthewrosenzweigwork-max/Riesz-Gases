import HRS.MS.R2InterpAux14
import HRS.Sections.Q17Aux3
import HRS.MC.S7PIS2RS

/-!
# S10.2 (worker S102), part 15 (packet I5): Riemann--Stieltjes integrals

`IsR2RS` is definitionally the torus `HRS.Sec7.IsRS`; the existence of the RS integral of a continuous operator-valued integrand against a
bounded-variation path (the case `Pj L = id` of `measure_projection_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

theorem s102_isR2RS_iff (T : ℝ) (S : ℝ → ℝ → ℝ → ℝ) (I : ℝ) : IsR2RS T S I ↔ HRS.Sec7.IsRS T S I := Iff.rfl

/-- Existence of the Riemann--Stieltjes integral of a continuous integrand against a BV path. -/
theorem s102_RS_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ}
    (hT : 0 < T) (F : ℝ → E) (hF : BoundedVariationOn F (Set.Icc 0 T)) (hF0 : F 0 = 0)
    (A : ℝ → (E →L[ℝ] ℝ)) (hA : ContinuousOn A (Set.Icc 0 T)) :
    ∃ I : ℝ, IsR2RS T (fun τ a b => A τ (F b - F a)) I := by
  obtain ⟨I, hI, -⟩ := HRS.Sec7.measure_projection_proof (fun _ => ContinuousLinearMap.id ℝ E) 1
    (fun _ => by simpa using ContinuousLinearMap.norm_id_le) (fun e => tendsto_const_nhds) T hT F hF hF0 A
    (fun _ => A) hA (fun _ => hA) (fun ε hε => ⟨0, fun L _ u _ => by simpa using hε.le⟩)
  exact ⟨I, hI⟩

/-- The Riemann--Stieltjes integral is unique. -/
theorem s102_RS_unique {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I I' : ℝ} (h : IsR2RS T S I)
    (h' : IsR2RS T S I') : I = I' :=
  HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT S I I' h h'

end HRS.MS.R2Interp

end
