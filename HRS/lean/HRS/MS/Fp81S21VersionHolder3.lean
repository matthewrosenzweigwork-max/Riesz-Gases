import HRS.MS.Fp81S21VersionHolder2

set_option autoImplicit false
noncomputable section

namespace HRS.Fp81.S21

/-- A dyadic scale can be chosen so that the geometric modulus with ratio
`9/10` is bounded by the eighth root of the normalized distance. -/
theorem fp81s21_dyadic_holder_scale {H d : ℝ}
    (hH : 0 < H) (hd : 0 < d) (hdH : d ≤ H) :
    ∃ m : ℕ, d ≤ H / 2 ^ m ∧
      (9 / 10 : ℝ) ^ m ≤ (2 * d / H) ^ (1 / 8 : ℝ) := by
  have hx0 : 0 < d / H := div_pos hd hH
  have hx1 : d / H ≤ 1 := (div_le_one hH).2 hdH
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near_of_lt_one hx0 hx1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  refine ⟨m, ?_, ?_⟩
  · have h := (div_le_iff₀ hH).1 hmhi
    rw [div_pow] at h
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · have hbase : (9 / 10 : ℝ) ^ 8 ≤ 1 / 2 := by norm_num
    have hpow : ((9 / 10 : ℝ) ^ m) ^ 8 ≤ (1 / 2 : ℝ) ^ m := by
      calc
        _ = ((9 / 10 : ℝ) ^ 8) ^ m := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase m
    have hlo : (1 / 2 : ℝ) ^ m ≤ 2 * d / H := by
      rw [pow_succ] at hmlo
      have h : (1 / 2 : ℝ) ^ m ≤ 2 * (d / H) := by nlinarith [hmlo]
      convert h using 1 <;> ring
    have hroot := (Real.le_rpow_inv_iff_of_pos
      (show 0 ≤ (9 / 10 : ℝ) ^ m by positivity)
      (show 0 ≤ 2 * d / H by positivity) (show (0 : ℝ) < 8 by norm_num)).2
        (by simpa only [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast] using hpow.trans hlo)
    simpa using hroot

#print axioms fp81s21_dyadic_holder_scale

end HRS.Fp81.S21
