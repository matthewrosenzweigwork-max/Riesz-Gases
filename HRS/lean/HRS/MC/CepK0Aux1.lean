import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Packet CEPK0 (aux 1): absolute continuity from a distance bound

Helper for `cep_K3_gronwall_ac_proof` (`HRS/MC/CepK0.lean`).
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace HRS.MC.CepK0

/-- A real function whose oscillation is dominated by a constant times an absolutely continuous
function is absolutely continuous (same squeeze as `LipschitzOnWith.comp_absolutelyContinuousOnInterval`). -/
theorem cep_K3_ac_of_dist_le {f g : ℝ → ℝ} {a b C : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ C * dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ (by simpa using Tendsto.const_mul C hg)
  · exact .of_forall fun _ ↦ by positivity
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦ hfg _ (hnI.left i hi).left _ (hnI.left i hi).right

end HRS.MC.CepK0
