import HRS.MS.R2S11Aux10

/-!
# S11.4 item (5), part 1: Hölder in time and the time-slice bound
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

/-- Jensen/Hölder in time: `(∫_I g)^q ≤ |I|^{q-1} ∫_I g^q` for `q ≥ 1`. -/
theorem s11_holder_time {q T : ℝ} (hq : 1 ≤ q) (I : Set ℝ) (hI : volume I = ENNReal.ofReal T)
    {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g (volume.restrict I)) :
    (∫⁻ t in I, g t) ^ q ≤ ENNReal.ofReal T ^ (q - 1) * ∫⁻ t in I, g t ^ q := by
  rcases hq.eq_or_lt with h1 | hq1
  · subst h1
    simp
  · have hpq : q.HolderConjugate q.conjExponent := Real.HolderConjugate.conjExponent hq1
    have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞)) (volume.restrict I) := aemeasurable_const
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict I) hpq hg hone
    simp only [Pi.mul_apply, mul_one, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ, hI] at h
    have hq0 : 0 < q := by linarith
    have h2 : (∫⁻ t in I, g t) ^ q ≤ ((∫⁻ t in I, g t ^ q) ^ (1 / q) * ENNReal.ofReal T ^ (1 / q.conjExponent)) ^ q :=
      ENNReal.rpow_le_rpow h hq0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
    have e1 : 1 / q * q = 1 := by field_simp
    have e2 : 1 / q.conjExponent * q = q - 1 := by
      have := hpq.inv_add_inv_eq_one
      have h3 : 1 / q.conjExponent = 1 - 1 / q := by
        have : q⁻¹ + q.conjExponent⁻¹ = 1 := this
        simp only [one_div]; linarith
      rw [h3]; field_simp
    rw [e1, e2, ENNReal.rpow_one] at h2
    rw [mul_comm]
    exact h2

end HRS.MS.R2S11
