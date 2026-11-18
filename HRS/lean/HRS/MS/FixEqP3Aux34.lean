import HRS.MS.FixEqP3Aux33

/-!
# S5.7 `fixed_equation` (worker S57P), part 46: the final real-number estimate
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

theorem s57p_final_real {Ca Cd Cp1 Cp2 S Cpp C0 Mg T : ℝ} (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) (hCp1 : 0 ≤ Cp1)
    (hCp2 : 0 ≤ Cp2) (hS : 0 ≤ S) (hCpp : 0 ≤ Cpp) (hC0 : 0 ≤ C0) (hMg : 0 ≤ Mg) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {aN a r1 r0 τ Dt : ℝ} (Ep : ℝ≥0∞), 0 ≤ r1 → 0 ≤ r0 → 0 ≤ τ → 0 ≤ Dt →
      2 * (ENNReal.ofReal (((|aN - a| * Ca + |a| * (Cp1 * Dt)) * Real.sqrt S) * Cpp) * Ep +
          (ENNReal.ofReal (C0 * (Mg * ((3 * s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt * S) ^ 2)))) ^ (1 / (4 : ℝ))) ≤
        ENNReal.ofReal C * ((ENNReal.ofReal |aN - a| + ENNReal.ofReal |a| * ENNReal.ofReal Dt) * Ep +
          (ENNReal.ofReal |r1 - r0| + ENNReal.ofReal r0 * (ENNReal.ofReal Dt + (ENNReal.ofReal τ) ^ (1 / (2 : ℝ))))) := by
  set K1 : ℝ := Cd ^ 2 * T ^ 2 + Ca ^ 2 with hK1
  set K2 : ℝ := Cp2 ^ 2 * T ^ 2 + Cp1 ^ 2 with hK2
  set cI : ℝ := max Ca Cp1 * Real.sqrt S * Cpp with hcI
  set cN : ℝ := (C0 * Mg) ^ (1 / (4 : ℝ)) * Real.sqrt (3 * S) * max (Real.sqrt (2 * K1)) (Real.sqrt (2 * K2)) with hcN
  have hcI0 : 0 ≤ cI := by rw [hcI]; exact mul_nonneg (mul_nonneg (le_max_of_le_left hCa) (Real.sqrt_nonneg _)) hCpp
  have hcN0 : 0 ≤ cN := by
    rw [hcN]; exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg hC0 hMg) _) (Real.sqrt_nonneg _))
      (le_max_of_le_left (Real.sqrt_nonneg _))
  refine ⟨2 * max cI cN, by positivity, ?_⟩
  intro aN a r1 r0 τ Dt Ep h1 h0 hτ hDt
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
  -- the initial part
  have hinit : ENNReal.ofReal (((|aN - a| * Ca + |a| * (Cp1 * Dt)) * Real.sqrt S) * Cpp) ≤
      ENNReal.ofReal cI * ENNReal.ofReal (|aN - a| + |a| * Dt) := by
    rw [← ENNReal.ofReal_mul hcI0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm1 : Ca ≤ max Ca Cp1 := le_max_left _ _
    have hm2 : Cp1 ≤ max Ca Cp1 := le_max_right _ _
    have h3 : (|aN - a| * Ca + |a| * (Cp1 * Dt)) ≤ max Ca Cp1 * (|aN - a| + |a| * Dt) := by
      have := abs_nonneg (aN - a); have := abs_nonneg a
      nlinarith [mul_le_mul_of_nonneg_left hm1 (abs_nonneg (aN - a)), mul_nonneg (abs_nonneg a) hDt,
        mul_le_mul_of_nonneg_left hm2 (mul_nonneg (abs_nonneg a) hDt)]
    calc (|aN - a| * Ca + |a| * (Cp1 * Dt)) * Real.sqrt S * Cpp
        ≤ max Ca Cp1 * (|aN - a| + |a| * Dt) * Real.sqrt S * Cpp :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)) hCpp
      _ = cI * (|aN - a| + |a| * Dt) := by rw [hcI]; ring
  -- the noise part
  have hZ : s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt =
      (2 * (r1 - r0) ^ 2 + 2 * r0 ^ 2 * τ) * K1 + 2 * r0 ^ 2 * Dt ^ 2 * K2 := by
    unfold s57pCz
    have e1 : Real.sqrt (2 * r1 ^ 2) = Real.sqrt 2 * r1 := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq h1]
    have e0 : Real.sqrt (2 * r0 ^ 2) = Real.sqrt 2 * r0 := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq h0]
    have e2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [e1, e0]
    have : (Real.sqrt 2 * r1 - Real.sqrt 2 * r0) ^ 2 = 2 * (r1 - r0) ^ 2 := by
      rw [← mul_sub, mul_pow, e2]
    rw [this, hK1, hK2]
  set a1 : ℝ := Real.sqrt (2 * K1) * |r1 - r0| with ha1
  set b1 : ℝ := Real.sqrt (2 * K1) * (r0 * Real.sqrt τ) with hb1
  set c1 : ℝ := Real.sqrt (2 * K2) * (r0 * Dt) with hc1
  have ha0 : 0 ≤ a1 := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hb0 : 0 ≤ b1 := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg h0 (Real.sqrt_nonneg _))
  have hc0 : 0 ≤ c1 := mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg h0 hDt)
  have hsq : s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt ≤ (a1 + b1 + c1) ^ 2 := by
    rw [hZ]
    have e1 : a1 ^ 2 = 2 * K1 * (r1 - r0) ^ 2 := by
      rw [ha1, mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    have e2 : b1 ^ 2 = 2 * K1 * (r0 ^ 2 * τ) := by
      rw [hb1, mul_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hτ]
    have e3 : c1 ^ 2 = 2 * K2 * (r0 ^ 2 * Dt ^ 2) := by
      rw [hc1, mul_pow, Real.sq_sqrt (by positivity), mul_pow]
    nlinarith [mul_nonneg ha0 hb0, mul_nonneg ha0 hc0, mul_nonneg hb0 hc0]
  have hZ0 : 0 ≤ s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt := by
    rw [hZ]; positivity
  have hsqrtZ : Real.sqrt (s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt) ≤ a1 + b1 + c1 := by
    calc _ ≤ Real.sqrt ((a1 + b1 + c1) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = a1 + b1 + c1 := Real.sqrt_sq (by positivity)
  set Z := s57pCz T (r0 ^ 2) (r1 ^ 2) τ Ca Cd Cp1 Cp2 Dt with hZdef
  have hy : 0 ≤ 3 * Z * S := mul_nonneg (mul_nonneg (by norm_num) hZ0) hS
  have hN0 : 0 ≤ C0 * (Mg * ((3 * Z * S) ^ 2)) := mul_nonneg hC0 (mul_nonneg hMg (sq_nonneg _))
  set mx : ℝ := max (Real.sqrt (2 * K1)) (Real.sqrt (2 * K2)) with hmx
  have hmx0 : 0 ≤ mx := le_max_of_le_left (Real.sqrt_nonneg _)
  have hδ0 : 0 ≤ |r1 - r0| := abs_nonneg _
  have hτ0' : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have habc : a1 + b1 + c1 ≤ mx * (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ) := by
    have h1' : Real.sqrt (2 * K1) ≤ mx := le_max_left _ _
    have h2' : Real.sqrt (2 * K2) ≤ mx := le_max_right _ _
    have := mul_le_mul_of_nonneg_right h1' hδ0
    have := mul_le_mul_of_nonneg_right h1' (mul_nonneg h0 hτ0')
    have := mul_le_mul_of_nonneg_right h2' (mul_nonneg h0 hDt)
    rw [ha1, hb1, hc1]; linarith
  have hnoise : (ENNReal.ofReal (C0 * (Mg * ((3 * Z * S) ^ 2)))) ^ (1 / (4 : ℝ)) ≤
      ENNReal.ofReal cN * ENNReal.ofReal (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hN0 (by norm_num), ← ENNReal.ofReal_mul hcN0]
    refine ENNReal.ofReal_le_ofReal ?_
    have e4 : ((3 * Z * S) ^ 2) ^ (1 / (4 : ℝ)) = Real.sqrt (3 * Z * S) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy, Real.sqrt_eq_rpow]; norm_num
    have e : (C0 * (Mg * ((3 * Z * S) ^ 2))) ^ (1 / (4 : ℝ)) =
        (C0 * Mg) ^ (1 / (4 : ℝ)) * Real.sqrt (3 * S) * Real.sqrt Z := by
      rw [← mul_assoc, Real.mul_rpow (mul_nonneg hC0 hMg) (sq_nonneg _), e4,
        show 3 * Z * S = (3 * S) * Z by ring, Real.sqrt_mul (mul_nonneg (by norm_num) hS)]
      ring
    rw [e, hcN]
    calc (C0 * Mg) ^ (1 / (4 : ℝ)) * Real.sqrt (3 * S) * Real.sqrt Z
        ≤ (C0 * Mg) ^ (1 / (4 : ℝ)) * Real.sqrt (3 * S) * (a1 + b1 + c1) :=
          mul_le_mul_of_nonneg_left hsqrtZ (mul_nonneg (Real.rpow_nonneg (mul_nonneg hC0 hMg) _) (Real.sqrt_nonneg _))
      _ ≤ (C0 * Mg) ^ (1 / (4 : ℝ)) * Real.sqrt (3 * S) * (mx * (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ)) :=
          mul_le_mul_of_nonneg_left habc (mul_nonneg (Real.rpow_nonneg (mul_nonneg hC0 hMg) _) (Real.sqrt_nonneg _))
      _ = _ := by ring
  -- the target
  have hr1 : ENNReal.ofReal |aN - a| + ENNReal.ofReal |a| * ENNReal.ofReal Dt = ENNReal.ofReal (|aN - a| + |a| * Dt) := by
    rw [ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg (abs_nonneg _) hDt), ENNReal.ofReal_mul (abs_nonneg _)]
  have hr2 : ENNReal.ofReal |r1 - r0| + ENNReal.ofReal r0 * (ENNReal.ofReal Dt + (ENNReal.ofReal τ) ^ (1 / (2 : ℝ))) =
      ENNReal.ofReal (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hτ (by norm_num), ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_add hDt hτ0',
      ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_add hδ0 (mul_nonneg h0 (add_nonneg hDt hτ0'))]
    congr 1; ring
  rw [hr1, hr2]
  have hm1 : ENNReal.ofReal cI ≤ ENNReal.ofReal (max cI cN) := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hm2 : ENNReal.ofReal cN ≤ ENNReal.ofReal (max cI cN) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc 2 * (ENNReal.ofReal (((|aN - a| * Ca + |a| * (Cp1 * Dt)) * Real.sqrt S) * Cpp) * Ep +
        (ENNReal.ofReal (C0 * (Mg * ((3 * Z * S) ^ 2)))) ^ (1 / (4 : ℝ)))
      ≤ 2 * (ENNReal.ofReal cI * ENNReal.ofReal (|aN - a| + |a| * Dt) * Ep +
        ENNReal.ofReal cN * ENNReal.ofReal (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ)) :=
        mul_le_mul' le_rfl (add_le_add (mul_le_mul' hinit le_rfl) hnoise)
    _ ≤ 2 * (ENNReal.ofReal (max cI cN) * (ENNReal.ofReal (|aN - a| + |a| * Dt) * Ep +
        ENNReal.ofReal (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ))) := by
        refine mul_le_mul' le_rfl ?_
        rw [mul_add]
        refine add_le_add ?_ (mul_le_mul' hm2 le_rfl)
        rw [mul_assoc]; exact mul_le_mul' hm1 le_rfl
    _ = ENNReal.ofReal (2 * max cI cN) * (ENNReal.ofReal (|aN - a| + |a| * Dt) * Ep +
        ENNReal.ofReal (|r1 - r0| + r0 * Dt + r0 * Real.sqrt τ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc]
        congr 1
        simp

end HRS.MS.FixEq
