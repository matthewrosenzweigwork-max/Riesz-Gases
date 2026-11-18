import HRS.MS.R26T6CI03

/-! R26-T6C.I04: centering is bounded by two on L3 of a probability measure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_centered_L3 (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (f : Euc d → ℝ) (hf : MemLp f 3 mu) :
    MemLp (HRS.Whole.projMean mu f) 3 mu ∧
    eLpNorm (HRS.Whole.projMean mu f) 3 mu ≤ 2 * eLpNorm f 3 mu := by
  have heq : HRS.Whole.projMean mu f = f - (fun _ => HRS.Whole.pair mu f) := by
    funext x
    rfl
  have hcenter : MemLp (HRS.Whole.projMean mu f) 3 mu := by
    rw [heq]
    exact hf.sub (memLp_const _)
  refine ⟨hcenter, ?_⟩
  have hmean : ‖HRS.Whole.pair mu f‖ₑ ≤ eLpNorm f 3 mu := by
    have h1 := enorm_integral_le_lintegral_enorm f (μ := mu)
    have h2 := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := mu)
      (show (1 : ℝ≥0∞) ≤ 3 by norm_num)
    have h1' : ‖∫ x, f x ∂mu‖ₑ ≤ eLpNorm f 1 mu := by
      simpa only [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable] using h1
    simpa only [HRS.Whole.pair] using h1'.trans h2
  have htriangle := eLpNorm_sub_le (f := f) (g := fun _ : Euc d => HRS.Whole.pair mu f)
    (μ := mu) (show (1 : ℝ≥0∞) ≤ 3 by norm_num)
  have hconst : eLpNorm (fun _ : Euc d => HRS.Whole.pair mu f) 3 mu = ‖HRS.Whole.pair mu f‖ₑ := by
    have hc := eLpNorm_const' (μ := mu) (p := (3 : ℝ≥0∞))
      (HRS.Whole.pair mu f) (by norm_num) (by norm_num)
    simpa [measure_univ] using hc
  rw [heq]
  calc
    _ ≤ eLpNorm f 3 mu + eLpNorm (fun _ : Euc d => HRS.Whole.pair mu f) 3 mu := by
      simpa only [Pi.sub_apply] using htriangle
    _ = eLpNorm f 3 mu + ‖HRS.Whole.pair mu f‖ₑ := by rw [hconst]
    _ ≤ eLpNorm f 3 mu + eLpNorm f 3 mu := add_le_add_right hmean _
    _ = 2 * eLpNorm f 3 mu := by ring

end HRS.MS.R26T6C
