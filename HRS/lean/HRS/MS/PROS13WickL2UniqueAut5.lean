import HRS.MS.PROS13WickRepAut5

/-!
# S13: uniqueness of an actual Gaussian L² limit

An L² sequence converging in mean square to two candidate random variables
has almost surely identical limits. This is valid for arbitrary probability
measures, including those supported on finitely many atoms.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem pro_s13_L2_squared_limit_unique
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Qj : ℕ → Ω → ℝ) (Q W : Ω → ℝ)
    (hQj : ∀ j, MemLp (Qj j) 2 P)
    (hQ : MemLp Q 2 P) (hW : MemLp W 2 P)
    (hQlim : Tendsto (fun j => ∫ ω, (Qj j ω - Q ω) ^ 2 ∂P)
      atTop (𝓝 0))
    (hWlim : Tendsto (fun j => ∫ ω, (Qj j ω - W ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Q =ᵐ[P] W := by
  exact TendstoL2.ae_unique
    (fun j => (hQj j).aestronglyMeasurable)
    (HRS.tendstoL2_of_memLp hQ hQj hQlim)
    (HRS.tendstoL2_of_memLp hW hQj hWlim)

#print axioms pro_s13_L2_squared_limit_unique
end HRS.MS.R26T3
