import HRS.MS.R26T6CI08
import HRS.MS.R2ChaosAux12

/-!
# S11.1 I09: summable square-integrable coordinates from L3 control
# This is the first input to the countable coordinate lift.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.R2Chaos

theorem r26t6c_coordinate_square_integral_summable
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {iota : Type*} (f : iota → Omega → ℝ) (b : iota → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Summable (fun i => b i ^ 2))
    (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    Summable (fun i => ∫ w, f i w ^ 2 ∂P) ∧
      ∀ i, ∫ w, f i w ^ 2 ∂P ≤ b i ^ 2 := by
  have h2 : ∀ i, MemLp (f i) 2 P := fun i =>
    (hf i).mono_exponent (by norm_num)
  have hle : ∀ i, ∫ w, f i w ^ 2 ∂P ≤ b i ^ 2 := by
    intro i
    apply s94_integral_sq_le_of_eLpNorm (h2 i).aestronglyMeasurable (hb0 i)
    exact (eLpNorm_le_eLpNorm_of_exponent_le
      (f := f i) (μ := P) (by norm_num : (2 : ℝ≥0∞) ≤ 3)).trans (hfb i)
  have hnonneg : ∀ i, 0 ≤ ∫ w, f i w ^ 2 ∂P :=
    fun i => integral_nonneg (fun w => sq_nonneg _)
  exact ⟨Summable.of_nonneg_of_le hnonneg hle hb, hle⟩

end HRS.MS.R26T6C
