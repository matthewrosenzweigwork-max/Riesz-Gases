import HRS.Main.ThermFinal

/-!
# THERM helper 10: limits of the right-hand sides of Corollary 2.7
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

/-- `ofReal u_N + ofReal (C e^{-c a_N}) (1 + K) → 0` for `u_N → 0`, `a_N → ∞`, `K < ∞`. -/
theorem therm_tendsto_rhs (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (C c : ℝ) (hc : 0 < c)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun N => ENNReal.ofReal (u N) +
      ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + K)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => ENNReal.ofReal (u N)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hu
  have h2 : Tendsto (fun N => C * Real.exp (-c * a N)) atTop (𝓝 0) := by
    have : Tendsto (fun N => -c * a N) atTop atBot :=
      ha.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul C
  have h3 : Tendsto (fun N => ENNReal.ofReal (C * Real.exp (-c * a N))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h2
  have h4 : Tendsto (fun N => ENNReal.ofReal (C * Real.exp (-c * a N)) * (1 + K)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const h3 (Or.inr (by simpa using hK))
  simpa using h1.add h4

end Main

end HRS
