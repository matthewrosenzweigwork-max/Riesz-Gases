import HRS.MS.Fp81S21WeightTrace
import HRS.MS.ProClosureS111ThermalTrace

/-!
# HRS S2.1(iii), physical reference thermal traces

This packages the value and commutator-kernel trace bounds for the two
weighted charts used by the physical Gaussian construction.  The constants
are selected before the trajectory and either chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The two thermal trace estimates supplied for one weighted chart and its
reference measure. -/
def fp81s21_thermal_chart_trace {d r : ℕ} {Pw : ℝ}
    (s : ℝ) (ρ : Euc d → ℝ) (E : r26t6_WeightedChart d r Pw) (B : ℝ) : Prop :=
  ((∀ j, MemLp (E.test j) 2 (HRS.Whole.withDensityReal ρ)) ∧
    Summable (fun j => ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal ρ) ∧
    (∑' j, ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal ρ) ≤ B) ∧
  ((∀ j, MemLp (fun xy : Euc d × Euc d =>
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) ∧
    Summable (fun j => ∫ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) ∧
    (∑' j, ∫ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) ≤ B)

/-- Uniform thermal trace bounds at the two frozen physical chart shapes.
Each bound is fixed before the trajectory and the charts, and the resulting
statements apply at the trajectory's reference density. -/
theorem fp81s21_physical_reference_thermal_traces (p : Parameters) :
    ∃ BEs BE : ℝ, 0 ≤ BEs ∧ 0 ≤ BE ∧
      ∀ δ : ℝ, ∀ R : Trajectory p δ,
        ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
        ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
          fp81s21_thermal_chart_trace p.s R.ρβ Es BEs ∧
          fp81s21_thermal_chart_trace p.s R.ρβ E BE := by
  have hdReal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
  have hrEs : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 6 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hPEs : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨BEs, hBEs, hTraceEs⟩ :=
    HRS.MS.ProClosureS111.physical_chart_thermal_traces p.hd p.s p.a p.β
      ((p.d : ℝ) + 4) (2 * p.d + 6) p.hs0 p.hs p.ha p.hβ hrEs hPEs
  have hrE : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  have hPE : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith
  obtain ⟨BE, hBE, hTraceE⟩ :=
    HRS.MS.ProClosureS111.physical_chart_thermal_traces p.hd p.s p.a p.β
      ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hrE hPE
  refine ⟨BEs, BE, hBEs, hBE, fun δ R Es E => ?_⟩
  constructor
  · simpa [fp81s21_thermal_chart_trace] using hTraceEs R.ρβ R.thermal Es
  · simpa [fp81s21_thermal_chart_trace] using hTraceE R.ρβ R.thermal E

#print axioms fp81s21_physical_reference_thermal_traces

end HRS.Fp81.S21

end
