import HRS.MS.ProClosureS111ChartedOrbits
import HRS.MS.ProClosureS111WindowOrbit
import HRS.MS.S111K4J01

/-!
Actual physical interval operators from the accepted bounded-operator
construction. The physical window-orbit input and charted measurability
are proved upstream, not assumed. The decay rate and operator bound are
chosen before the thermal density, the chart, and the window start.

Existence of a weighted chart is a separate Hilbert-space construction.
The result here works for every chart satisfying the exact frozen chart
definition. No random-field or source-contraction data are assumed or
claimed to be constructed by this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111K2 HRS.MS.S111K4J01 HRS.MS.R26T6

variable {d r : ℕ} {Pw : ℝ}

/-- The accepted and frozen interval structures have identical data.
Every coordinate and norm field is retained by this conversion. -/
def frozenIntervalOfNative (E : r26t6_WeightedChart d r Pw)
    {C : WholeCoeff d} {T u c0 B : ℝ}
    (O : IntervalOperators (nativeChartOfFrozen E) C T u c0 B) :
    r26t6_IntervalOperators E C T u c0 B where
  drift := O.drift
  covariance := O.covariance
  drift_zero := O.drift_zero
  covariance_zero := O.covariance_zero
  drift_add := O.drift_add
  covariance_add := O.covariance_add
  drift_cont := O.drift_cont
  covariance_cont := O.covariance_cont
  drift_norm := O.drift_norm
  covariance_norm := O.covariance_norm
  drift_coordinate := O.drift_coordinate
  covariance_coordinate := O.covariance_coordinate

/-- Physical interval maps for an arbitrary admissible weight. Constants
precede all equilibria, charts, and window starts. -/
theorem physical_interval_operators (hd : 2 ≤ d)
    (s a beta T Pw : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) (hT : 0 < T)
    (hPw : (d : ℝ) / 2 + 1 < Pw) :
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ E : r26t6_WeightedChart d (r26t6_coreOrder d) Pw,
      ∀ u : ℝ, 0 ≤ u →
        Nonempty (r26t6_IntervalOperators E (r26t6_thermalCoeff d s a beta rho)
          T u c0 B) := by
  obtain ⟨c0, b, hc0, hbs, hW⟩ :=
    physical_window_orbit_input hd s a beta hs0 hsd ha hbeta
  let S : ℝ := ∑' alpha, b alpha ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun _ => sq_nonneg _
  have hr : (d : ℝ) / 2 + 2 < r26t6_coreOrder d := by
    unfold r26t6_coreOrder
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨B, hB, hO⟩ := k4_coefficient_interval_operators d (r26t6_coreOrder d)
    hd T Pw S c0 hT hPw hr hS hc0
  refine ⟨c0, B, hc0, hB, ?_⟩
  intro rho hrho E u hu
  have hP : (d : ℝ) < 2 * Pw := by linarith
  have hco := physical_charted_orbits hd hs0 hsd ha hbeta hrho
    (add_nonneg hu hT.le) hP (nativeChartOfFrozen E)
  obtain ⟨O⟩ := hO (nativeChartOfFrozen E) (r26t6_thermalCoeff d s a beta rho)
    b hbs le_rfl (hW rho hrho) u hu hco
  exact ⟨frozenIntervalOfNative E O⟩

/-- The complete deterministic interval data at the exact frozen orders.
Both the charted-orbit premise and the original all-test approximation are
produced from the physical assumptions. The eventual chart construction
can instantiate this theorem without any further propagator premise. -/
theorem physical_core_interval_data (hd : 2 ≤ d)
    (s a beta T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hT : 0 < T) :
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ E : r26t6_WeightedChart d (r26t6_coreOrder d) (r26t6_coreWeight d),
      ∀ u : ℝ, 0 ≤ u →
        r26t6_ChartedOrbits E (r26t6_thermalCoeff d s a beta rho)
          (wholeSpaceIndex d) (u + T) ∧
        r26t6_OscOrbitApprox (r26t6_thermalCoeff d s a beta rho)
          (wholeSpaceIndex d) (u + T) (r26t6_coreOrder d) ∧
        Nonempty (r26t6_IntervalOperators E (r26t6_thermalCoeff d s a beta rho)
          T u c0 B) := by
  have hsd : s < (d : ℝ) := by
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hPw : (d : ℝ) / 2 + 1 < r26t6_coreWeight d := by
    unfold r26t6_coreWeight
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨c0, B, hc0, hB, hO⟩ := physical_interval_operators hd s a beta T
    (r26t6_coreWeight d) hs0 hsd ha hbeta hT hPw
  refine ⟨c0, B, hc0, hB, fun rho hrho E u hu => ?_⟩
  have hP : (d : ℝ) < 2 * r26t6_coreWeight d := by linarith
  exact ⟨physical_frozen_charted_orbits hd hs0 hsd ha hbeta hrho
      (add_nonneg hu hT.le) hP E,
    physical_frozen_osc_orbit_approx hd hs0 hs ha hbeta hrho (add_nonneg hu hT.le),
    hO rho hrho E u hu⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_interval_operators
#print axioms HRS.MS.ProClosureS111.physical_core_interval_data
