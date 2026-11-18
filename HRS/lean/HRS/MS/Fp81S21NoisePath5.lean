import HRS.MS.Fp81S21NoisePath4

/-! Deterministic horizon envelope for the sixth moment. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21

/-- Absorb all horizon-independent factors into one constant before choosing `H`. -/
theorem fp81s21_noisePath_horizon_envelope (c a C H : ℝ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    (3 + Real.sqrt H) ^ 6 * c * (H * (a * (C * (1 + Real.sqrt H)) ^ 2)) ^ 3 ≤
      ((3 * (c + 1) * (a + 1) * C) * (1 + Real.sqrt H) ^ 3) ^ 6 := by
  let x := Real.sqrt H
  have hx : 0 ≤ x := Real.sqrt_nonneg H
  have hxx : x ^ 2 = H := Real.sq_sqrt hH
  have hc6 : c ≤ (c + 1) ^ 6 :=
    (show c ≤ c + 1 by linarith).trans (le_self_pow₀ (by linarith) (by norm_num))
  have ha2 : a ≤ (a + 1) ^ 2 := by nlinarith [sq_nonneg a]
  have hx2 : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
  have h3 : 3 + x ≤ 3 * (1 + x) := by linarith
  change (3 + x) ^ 6 * c * (H * (a * (C * (1 + x)) ^ 2)) ^ 3 ≤
    ((3 * (c + 1) * (a + 1) * C) * (1 + x) ^ 3) ^ 6
  rw [← hxx]
  calc
    _ ≤ (3 * (1 + x)) ^ 6 * (c + 1) ^ 6 *
        ((1 + x) ^ 2 * ((a + 1) ^ 2 * (C * (1 + x)) ^ 2)) ^ 3 := by
      gcongr
    _ = _ := by
      generalize 1 + x = y
      generalize c + 1 = z
      generalize a + 1 = w
      ring

#print axioms HRS.Fp81.S21.fp81s21_noisePath_horizon_envelope
end HRS.Fp81.S21
