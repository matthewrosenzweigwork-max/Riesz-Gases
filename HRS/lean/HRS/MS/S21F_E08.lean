import HRS.MP.SelfSimP4Gibbs

/-!
# S21F, packet R26-T3.E08: entropy tensorization with a common noise law

`klDiv (μ ⊗ W) (ν ⊗ W) = klDiv μ ν` for a common probability factor `W` (extended KL, no finiteness or
positivity hypothesis), from the Mathlib chain rule `klDiv_compProd_left` with the constant kernel.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T3

theorem r26t3_entropy_product {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ ν : Measure E) (W : Measure F) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure W] :
    InformationTheory.klDiv (μ.prod W) (ν.prod W) = InformationTheory.klDiv μ ν := by
  rw [← Measure.compProd_const, ← Measure.compProd_const]
  exact klDiv_compProd_left μ ν (Kernel.const E W)

end HRS.MS.R26T3
