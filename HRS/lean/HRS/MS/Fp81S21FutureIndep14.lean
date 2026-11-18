import HRS.MS.Fp81S21FutureIndep7
import HRS.MS.GenPathAux56

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.GenPath

/-- Reconstruct a measurable path on the same source space from its dense
coordinate array, once that array has the law of a continuous path. -/
theorem fp81s21_path_from_coordinate_law
    {d : ℕ} {m H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : Measure (OscPath d m H))
    (s : ℕ → Icc (0 : ℝ) H) (hs : DenseRange s)
    (U : Ω → (ℕ × MultiIndex d → ℝ)) (hUm : Measurable U)
    (hlaw : P.map U = γ.map (s56PathCoords (d := d) m H s)) :
    ∃ X : Ω → OscPath d m H, Measurable X ∧ P.map X = γ ∧
      ∀ᵐ ω ∂P, ∀ i, OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 = U ω i := by
  let Ψ := s56PathCoords (d := d) m H s
  have hemb := s56_measurableEmbedding_pathCoords (d := d) m H s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  have hrange : ∀ᵐ ω ∂P, U ω ∈ Set.range Ψ :=
    s56_ae_mem_of_map_eq P γ U Ψ hUm.aemeasurable hemb.measurable.aemeasurable
      hlaw hemb.measurableSet_range (Filter.Eventually.of_forall fun w => ⟨w, rfl⟩)
  refine ⟨g ∘ U, hgm.comp hUm, ?_, ?_⟩
  · rw [← Measure.map_map hgm hUm, hlaw, Measure.map_map hgm hemb.measurable]
    simpa using congrArg (Measure.map · γ) hg
  · filter_upwards [hrange] with ω hω
    obtain ⟨w, hw⟩ := hω
    have hg' : g (Ψ w) = w := congrFun hg w
    simp only [Function.comp_apply]
    rw [← hw, hg']
    intro i
    rfl

#print axioms fp81s21_path_from_coordinate_law

end HRS.Fp81.S21
end
