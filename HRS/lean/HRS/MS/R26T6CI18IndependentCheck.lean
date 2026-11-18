import HRS.MS.R26T6CI18

-- Independently copied pinned definition and theorem, no weakened hypotheses.
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6C
open HRS
open HRS.Whole
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

def r26t6c_toLp3_independent_pinned_def {X : Type*} [MeasurableSpace X] (mu : Measure X) (f : X → ℝ) : Lp ℝ 3 mu :=
  if h : MemLp f 3 mu then h.toLp f else 0

theorem r26t6c_L3_hasDerivAt_independent_pinned_consumer {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w w' : ℝ → X → ℝ) (G : X → ℝ)
    (a b t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hw : ∀ q ∈ Set.Ioo a b, MemLp (w q) 3 mu)
    (hw' : MemLp (w' t) 3 mu) (hG : MemLp G 3 mu)
    (hder : ∀ x q, q ∈ Set.Ioo a b → HasDerivAt (fun r => w r x) (w' q x) q)
    (hbd : ∀ q ∈ Set.Ioo a b, ∀ x, |w' q x| ≤ G x) :
    HasDerivAt (fun q => r26t6c_toLp3 mu (w q)) (r26t6c_toLp3 mu (w' t)) t := by
  exact r26t6c_L3_hasDerivAt mu w w' G a b t ht hw hw' hG hder hbd


theorem r26t6c_i18_definitional_check {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ) :
    r26t6c_toLp3_independent_pinned_def mu f = r26t6c_toLp3 mu f := rfl

#print axioms HRS.MS.R26T6C.r26t6c_L3_hasDerivAt
#print axioms HRS.MS.R26T6C.r26t6c_L3_hasDerivAt_independent_pinned_consumer
#print axioms HRS.MS.R26T6C.r26t6c_i18_definitional_check
end HRS.MS.R26T6C
