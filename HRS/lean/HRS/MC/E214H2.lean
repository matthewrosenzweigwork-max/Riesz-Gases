import HRS.MC.E214H1
import HRS.Prob.Metrics

/-!
# E214H2: transfer lemmas for `covDist`

If the laws of two pairs of random elements agree, the integrals of every continuous function agree, hence so
do the `covDist`.  A pathwise sup-norm bound of a continuous path by an `iSup` of `ENNReal` norms.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MC.E214H

section Transfer

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem integral_comp_of_law_eq {P : Measure Ω} {P' : Measure Ω'} {X : Ω → B} {W : Ω' → B}
    (hX : AEMeasurable X P) (hW : AEMeasurable W P') (h : law P X = law P' W) {g : B → ℝ}
    (hg : Continuous g) : ∫ ω, g (X ω) ∂P = ∫ ω, g (W ω) ∂P' := by
  have e1 := integral_map (μ := P) hX hg.aestronglyMeasurable (f := g)
  have e2 := integral_map (μ := P') hW hg.aestronglyMeasurable (f := g)
  have : ∫ x, g x ∂(law P X) = ∫ x, g x ∂(law P' W) := by rw [h]
  exact e1.symm.trans (this.trans e2)

theorem integrable_comp_of_law_eq {P : Measure Ω} {P' : Measure Ω'} {X : Ω → B} {W : Ω' → B}
    (hX : AEMeasurable X P) (hW : AEMeasurable W P') (h : law P X = law P' W) {g : B → ℝ}
    (hg : Continuous g) (hi : Integrable (fun ω => g (W ω)) P') : Integrable (fun ω => g (X ω)) P := by
  have i2 : Integrable g (law P' W) := (integrable_map_measure hg.aestronglyMeasurable hW).2 hi
  rw [← h] at i2
  exact (integrable_map_measure hg.aestronglyMeasurable hX).1 i2

theorem covDist_of_law_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P' : Measure Ω'} {Q : Measure Ω₁} {Q' : Measure Ω₂}
    {X : Ω → B} {W : Ω' → B} {X' : Ω₁ → B} {W' : Ω₂ → B}
    (hX : AEMeasurable X P) (hW : AEMeasurable W P') (h : law P X = law P' W)
    (hX' : AEMeasurable X' Q) (hW' : AEMeasurable W' Q') (h' : law Q X' = law Q' W') :
    HRS.Main.covDist P Q X X' = HRS.Main.covDist P' Q' W W' := by
  unfold HRS.Main.covDist
  congr 1
  funext M
  rw [integral_comp_of_law_eq hX hW h (continuous_quad M.1),
    integral_comp_of_law_eq hX' hW' h' (continuous_quad M.1)]

end Transfer

end HRS.MC.E214H

end
