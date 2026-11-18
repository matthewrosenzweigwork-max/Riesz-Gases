import HRS.MP.SelfSimP4LscM

/-!
# S21F, packet R26-T3.E13: eventual equality implies bounded-measurable convergence of laws

Contract repair (elaboration only): `HRS.law` needs a normed target `B`, while the contract has `E` only a
measurable space; `law P Y` is by definition `P.map Y` (`abbrev`), so the statement is written with `P.map`
(identical for normed `E`, and the same statement in general).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T3

theorem r26t3_eventual_law_convergence {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (X : Ω → E)
    (hY : ∀ n, AEMeasurable (Y n) P) (hX : AEMeasurable X P)
    (heq : ∀ᵐ ζ ∂P, ∀ᶠ n : ℕ in atTop, Y n ζ = X ζ) :
    ∀ f : E → ℝ, Measurable f → (∃ B, ∀ x, |f x| ≤ B) →
      Tendsto (fun n => ∫ x, f x ∂(P.map (Y n))) atTop (𝓝 (∫ x, f x ∂(P.map X))) := by
  intro f hf ⟨B, hB⟩
  have h1 : ∀ n, ∫ x, f x ∂(P.map (Y n)) = ∫ ζ, f (Y n ζ) ∂P := fun n =>
    integral_map (hY n) hf.aestronglyMeasurable
  rw [integral_map hX hf.aestronglyMeasurable]
  simp_rw [h1]
  refine tendsto_integral_of_dominated_convergence (fun _ => |B|) ?_ ?_ ?_ ?_
  · exact fun n => (hf.comp_aemeasurable (hY n)).aestronglyMeasurable
  · exact integrable_const _
  · exact fun n => Filter.Eventually.of_forall fun ζ =>
      by simpa using (hB (Y n ζ)).trans (le_abs_self B)
  · filter_upwards [heq] with ζ hζ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hζ] with n hn
    rw [hn]

end HRS.MS.R26T3
