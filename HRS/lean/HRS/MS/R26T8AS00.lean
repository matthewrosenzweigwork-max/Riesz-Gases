import HRS.MS.R26T8AD01

/-!
# S8.2 observed-time layer, packet T8A.S00: closed progressive span in the finite-noise L2 space

`r26t8a_progSpan P F b` is the topological closure of the linear span of the native embeddings `embL2 hH b` of
progressive L2 integrands. `r26t8a_progEmbed` exhibits each such embedding as an element of the closed span.
No new stochastic integral is constructed here.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

/-- the closed linear span of the progressive L2 embeddings -/
def r26t8a_progSpan {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ) :
    Submodule ℝ (Lp (EuclideanSpace ℝ I) 2 (HRS.tsMeasure P b)) :=
  (Submodule.span ℝ {v | ∃ H : ℝ → Omega → I → ℝ,
    ∃ hH : IsProgressiveL2 P F H, v = HRS.embL2 hH b}).topologicalClosure

/-- each progressive embedding lies in the closed span -/
def r26t8a_progEmbed {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b : ℝ)
    (H : ℝ → Omega → I → ℝ) (hH : IsProgressiveL2 P F H) : r26t8a_progSpan (I := I) P F b :=
  ⟨HRS.embL2 hH b, Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨H, hH, rfl⟩)⟩

end HRS.MS.R26T8A

end
