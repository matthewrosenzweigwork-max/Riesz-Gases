import HRS.MS.ProClosureS111WeightedChart
import HRS.MS.ProClosureS111IntervalOperators

/-!
Concrete realization of the frozen deterministic chart-and-interval
branch. The chart, decay rate, and operator bound are all chosen before
the thermal density and the window start. The original charted orbits and
all-test oscillator approximation are produced, not postulated.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6

variable {d : ℕ}

theorem physical_core_weighted_chart (hd : 0 < d) :
    Nonempty (r26t6_WeightedChart d (r26t6_coreOrder d) (r26t6_coreWeight d)) := by
  apply physical_weighted_chart hd
  unfold r26t6_coreWeight
  linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- A genuine chart and the exact frozen interval data, from physical
parameters only. This includes every start time and every equilibrium
under one pair of constants and one chart. -/
theorem physical_core_chart_interval_data (hd : 2 ≤ d)
    (s a beta T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hT : 0 < T) :
    ∃ E : r26t6_WeightedChart d (r26t6_coreOrder d) (r26t6_coreWeight d),
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ u : ℝ, 0 ≤ u →
        r26t6_ChartedOrbits E (r26t6_thermalCoeff d s a beta rho)
          (wholeSpaceIndex d) (u + T) ∧
        r26t6_OscOrbitApprox (r26t6_thermalCoeff d s a beta rho)
          (wholeSpaceIndex d) (u + T) (r26t6_coreOrder d) ∧
        Nonempty (r26t6_IntervalOperators E (r26t6_thermalCoeff d s a beta rho)
          T u c0 B) := by
  obtain ⟨E⟩ := physical_core_weighted_chart (show 0 < d by omega)
  obtain ⟨c0, B, hc0, hB, hdata⟩ :=
    physical_core_interval_data hd s a beta T hs0 hs ha hbeta hT
  exact ⟨E, c0, B, hc0, hB, fun rho hrho u hu => hdata rho hrho E u hu⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_core_weighted_chart
#print axioms HRS.MS.ProClosureS111.physical_core_chart_interval_data
