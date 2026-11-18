import HRS.MS.R26T6CI18
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6C
open HRS HRS.Whole
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
theorem r26t6c_L3_hasDerivAt_exact_pinned_consumer {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w w' : ℝ → X → ℝ) (G : X → ℝ)
    (a b t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hw : ∀ q ∈ Set.Ioo a b, MemLp (w q) 3 mu)
    (hw' : MemLp (w' t) 3 mu) (hG : MemLp G 3 mu)
    (hder : ∀ x q, q ∈ Set.Ioo a b → HasDerivAt (fun r => w r x) (w' q x) q)
    (hbd : ∀ q ∈ Set.Ioo a b, ∀ x, |w' q x| ≤ G x) :
    HasDerivAt (fun q => r26t6c_toLp3 mu (w q)) (r26t6c_toLp3 mu (w' t)) t := by
  exact r26t6c_L3_hasDerivAt mu w w' G a b t ht hw hw' hG hder hbd

#print axioms r26t6c_L3_hasDerivAt
#print axioms r26t6c_L3_hasDerivAt_exact_pinned_consumer
end HRS.MS.R26T6C
