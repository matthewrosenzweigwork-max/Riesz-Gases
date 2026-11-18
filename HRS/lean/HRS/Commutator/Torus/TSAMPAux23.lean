import HRS.Commutator.Torus.TSAMPAux22

/-!
# T-SAMP helpers, part 23: real-variable inequalities for the profile majorant
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

lemma tsamp_far_real {η t t' e Cm D : ℝ} {M : ℕ} (hη : 0 < η) (hCm : 0 ≤ Cm) (ht : η ≤ t)
    (ht' : 0 ≤ t') (hD : 0 ≤ D) (htt : t' ≤ t + D * η) :
    Cm * η ^ (e + (M : ℝ)) * t ^ (-(M : ℝ)) ≤
      (Cm * 2 ^ M * (1 + D) ^ M * η ^ e) * (1 + t' / η) ^ (-(M : ℝ)) := by
  have htpos : 0 < t := lt_of_lt_of_le hη ht
  set s : ℝ := t / η with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hη]; linarith
  have hspos : 0 < s := by linarith
  have h1 : t ^ (-(M : ℝ)) = η ^ (-(M : ℝ)) * s ^ (-(M : ℝ)) := by
    rw [hs, ← Real.mul_rpow hη.le (div_nonneg htpos.le hη.le), mul_div_cancel₀ _ hη.ne']
  have h2 : η ^ (e + (M : ℝ)) * η ^ (-(M : ℝ)) = η ^ e := by
    rw [← Real.rpow_add hη]; simp
  have hq0 : 0 < 1 + t' / η := by positivity
  have hq : 1 + t' / η ≤ (1 + D) * (2 * s) := by
    have e1 : t' / η ≤ s + D := by
      rw [hs, ← sub_nonneg]
      have : s + D - t' / η = (t + D * η - t') / η := by rw [hs]; field_simp
      rw [show t / η + D - t' / η = (t + D * η - t') / η by field_simp]
      exact div_nonneg (by linarith) hη.le
    nlinarith
  have hpow : (1 + t' / η) ^ (M : ℕ) ≤ ((1 + D) * (2 * s)) ^ (M : ℕ) :=
    pow_le_pow_left₀ hq0.le hq M
  have key : s ^ (-(M : ℝ)) ≤ 2 ^ M * (1 + D) ^ M * (1 + t' / η) ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg hspos.le, Real.rpow_neg hq0.le, Real.rpow_natCast, Real.rpow_natCast]
    rw [mul_pow, mul_pow] at hpow
    have hs0 : 0 < s ^ M := pow_pos hspos M
    have hq1 : 0 < (1 + t' / η) ^ M := pow_pos hq0 M
    have hA : 0 < (2 : ℝ) ^ M * (1 + D) ^ M := by positivity
    have h3 : (1 + t' / η) ^ M ≤ ((2 : ℝ) ^ M * (1 + D) ^ M) * s ^ M := by
      calc (1 + t' / η) ^ M ≤ (1 + D) ^ M * (2 ^ M * s ^ M) := hpow
        _ = ((2 : ℝ) ^ M * (1 + D) ^ M) * s ^ M := by ring
    calc (s ^ M)⁻¹ = ((2 : ℝ) ^ M * (1 + D) ^ M) * (((2 : ℝ) ^ M * (1 + D) ^ M) * s ^ M)⁻¹ := by
          field_simp
      _ ≤ ((2 : ℝ) ^ M * (1 + D) ^ M) * ((1 + t' / η) ^ M)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hq1 h3) hA.le
  calc Cm * η ^ (e + (M : ℝ)) * t ^ (-(M : ℝ)) = Cm * (η ^ (e + (M : ℝ)) * η ^ (-(M : ℝ))) * s ^ (-(M : ℝ)) := by
        rw [h1]; ring
    _ = Cm * η ^ e * s ^ (-(M : ℝ)) := by rw [h2]
    _ ≤ Cm * η ^ e * (2 ^ M * (1 + D) ^ M * (1 + t' / η) ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (Cm * 2 ^ M * (1 + D) ^ M * η ^ e) * (1 + t' / η) ^ (-(M : ℝ)) := by ring

end HRS.Commutator.TorusNote
