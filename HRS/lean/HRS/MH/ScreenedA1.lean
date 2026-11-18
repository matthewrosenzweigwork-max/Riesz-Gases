import HRS.MH.ScreenedDefs
import HRS.Commutator.Whole.LocalAuxSAMP1

/-!
# Packet A1 of `B:lem:screened` (S.B.4): Young `L¹ * L²` in `ℝ≥0∞` form.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem young_l1_l2_proof (k f : Euc d → ℝ≥0∞) (hk : Measurable k) (hf : Measurable f)
    (hk1 : ∫⁻ y, k y ≠ ⊤) :
    ∫⁻ x, (∫⁻ y, k (x - y) * f y) ^ 2 ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ y, f y ^ 2 := by
  have h := HRS.Commutator.Whole.SAMP1.young_lintegral (volume : Measure (Euc d)) (k := k) (f := f) hk hf
    (p := 2) (by norm_num) hk1
  have e1 : ∀ x : Euc d, ∫⁻ y, k (x - y) * f y = ∫⁻ y, k y * f (x - y) := by
    intro x
    have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun y => k y * f (x - y)) x
    simp only [sub_sub_cancel] at this
    exact this
  simp_rw [e1]
  simpa only [ENNReal.rpow_two] using h

end HRS.MH.Screened
