import HRS.MS.R26T8AC07c

/-!
# S8.2 observed-time layer, packet T8A.C07d: evaluation of the two-centre bound with exponents `(d/2, d/4)` for `D < 2`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A

theorem r26t8a_c07d_eval (d : ℕ) (hd : 1 ≤ d) {D R : ℝ} (hD : 0 < D) (hD2 : D < 2) (hR1 : R ≤ 1) :
    ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 4))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - (d : ℝ) / 2)) +
      ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - (d : ℝ) / 4)) +
      ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2 + (d : ℝ) / 4))) *
        ENNReal.ofReal (r26t8a_c08a_const d * ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0)) +
      ENNReal.ofReal (2 ^ ((d : ℝ) / 4)) *
        ENNReal.ofReal (r26t8a_c08a_const d *
          ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - ((d : ℝ) / 2 + (d : ℝ) / 4))) ≤
      ENNReal.ofReal (r26t8a_c08a_const d * (1 / ((d : ℝ) / 2) + 1 / ((d : ℝ) - (d : ℝ) / 4) + 4 ^ d / d +
        2 ^ ((d : ℝ) / 4) * (5 ^ ((d : ℝ) / 4) / ((d : ℝ) / 4)))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set ω : ℝ := r26t8a_c08a_const d with hω
  have hω0 : 0 ≤ ω := r26t8a_c08a_const_nonneg d
  set θ : ℝ := (d : ℝ) / 4 with hθ
  have hθ0 : 0 < θ := by positivity
  have hD2' : 0 < D / 2 := by positivity
  have hDθ : (D / 2) ^ θ ≤ 1 := Real.rpow_le_one hD2'.le (by linarith) hθ0.le
  have hDθ0 : 0 ≤ (D / 2) ^ θ := Real.rpow_nonneg hD2'.le _
  have hee : (d : ℝ) / 2 = θ + θ := by rw [hθ]; ring
  -- T1
  have hI1 : ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - (d : ℝ) / 2) = (D / 2) ^ ((d : ℝ) / 2) / ((d : ℝ) / 2) := by
    have hex : (d : ℝ) - 1 - (d : ℝ) / 2 + 1 = (d : ℝ) / 2 := by ring
    rw [integral_rpow (Or.inl (by linarith)), hex, Real.zero_rpow (by positivity)]; simp
  have t1 : ENNReal.ofReal ((D / 2) ^ (-θ)) * ENNReal.ofReal (ω * ∫ r in (0 : ℝ)..(D / 2),
      r ^ ((d : ℝ) - 1 - (d : ℝ) / 2)) ≤ ENNReal.ofReal (ω * (1 / ((d : ℝ) / 2))) := by
    rw [hI1, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2'.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (D / 2) ^ (-θ) * (D / 2) ^ ((d : ℝ) / 2) = (D / 2) ^ θ := by
      rw [← Real.rpow_add hD2']; congr 1; rw [hee]; ring
    calc (D / 2) ^ (-θ) * (ω * ((D / 2) ^ ((d : ℝ) / 2) / ((d : ℝ) / 2))) =
        ((D / 2) ^ (-θ) * (D / 2) ^ ((d : ℝ) / 2)) * (ω * (1 / ((d : ℝ) / 2))) := by ring
      _ = (D / 2) ^ θ * (ω * (1 / ((d : ℝ) / 2))) := by rw [this]
      _ ≤ 1 * (ω * (1 / ((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_right hDθ (by positivity)
      _ = _ := one_mul _
  -- T2
  have hI2 : ∫ r in (0 : ℝ)..(D / 2), r ^ ((d : ℝ) - 1 - θ) = (D / 2) ^ ((d : ℝ) - θ) / ((d : ℝ) - θ) := by
    have hex : (d : ℝ) - 1 - θ + 1 = (d : ℝ) - θ := by ring
    rw [integral_rpow (Or.inl (by rw [hθ]; linarith)), hex, Real.zero_rpow (by rw [hθ]; linarith)]; simp
  have t2 : ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2))) * ENNReal.ofReal (ω * ∫ r in (0 : ℝ)..(D / 2),
      r ^ ((d : ℝ) - 1 - θ)) ≤ ENNReal.ofReal (ω * (1 / ((d : ℝ) - θ))) := by
    rw [hI2, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2'.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdθ : 0 < (d : ℝ) - θ := by rw [hθ]; linarith
    have : (D / 2) ^ (-((d : ℝ) / 2)) * (D / 2) ^ ((d : ℝ) - θ) = (D / 2) ^ θ := by
      rw [← Real.rpow_add hD2']; congr 1; rw [hθ]; ring
    calc (D / 2) ^ (-((d : ℝ) / 2)) * (ω * ((D / 2) ^ ((d : ℝ) - θ) / ((d : ℝ) - θ))) =
        ((D / 2) ^ (-((d : ℝ) / 2)) * (D / 2) ^ ((d : ℝ) - θ)) * (ω * (1 / ((d : ℝ) - θ))) := by ring
      _ = (D / 2) ^ θ * (ω * (1 / ((d : ℝ) - θ))) := by rw [this]
      _ ≤ 1 * (ω * (1 / ((d : ℝ) - θ))) := mul_le_mul_of_nonneg_right hDθ (by positivity)
      _ = _ := one_mul _
  -- T3
  have hI3 : ∫ r in (0 : ℝ)..(2 * D), r ^ ((d : ℝ) - 1 - 0) = (2 * D) ^ (d : ℝ) / d := by
    have hex : (d : ℝ) - 1 - 0 + 1 = d := by ring
    rw [integral_rpow (Or.inl (by linarith)), hex, Real.zero_rpow hdR.ne']; simp
  have t3 : ENNReal.ofReal ((D / 2) ^ (-((d : ℝ) / 2 + θ))) * ENNReal.ofReal (ω * ∫ r in (0 : ℝ)..(2 * D),
      r ^ ((d : ℝ) - 1 - 0)) ≤ ENNReal.ofReal (ω * (4 ^ d / d)) := by
    rw [hI3, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD2'.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2D : (2 * D) = 4 * (D / 2) := by ring
    rw [h2D, Real.mul_rpow (by norm_num) hD2'.le, Real.rpow_natCast]
    have : (D / 2) ^ (-((d : ℝ) / 2 + θ)) * (D / 2) ^ (d : ℝ) = (D / 2) ^ θ := by
      rw [← Real.rpow_add hD2']; congr 1; rw [hθ]; ring
    calc (D / 2) ^ (-((d : ℝ) / 2 + θ)) * (ω * (4 ^ d * (D / 2) ^ (d : ℝ) / d)) =
        ((D / 2) ^ (-((d : ℝ) / 2 + θ)) * (D / 2) ^ (d : ℝ)) * (ω * (4 ^ d / d)) := by ring
      _ = (D / 2) ^ θ * (ω * (4 ^ d / d)) := by rw [this]
      _ ≤ 1 * (ω * (4 ^ d / d)) := mul_le_mul_of_nonneg_right hDθ (by positivity)
      _ = _ := one_mul _
  -- T4
  have hex4 : (d : ℝ) - 1 - ((d : ℝ) / 2 + θ) + 1 = θ := by rw [hθ]; ring
  have hmaxpos : 0 < 2 * D := by linarith
  have hI4 : ∫ r in (2 * D)..(max (2 * D) R), r ^ ((d : ℝ) - 1 - ((d : ℝ) / 2 + θ)) =
      ((max (2 * D) R) ^ θ - (2 * D) ^ θ) / θ := by
    rw [integral_rpow (Or.inl (by rw [hθ]; linarith)), hex4]
  have t4 : ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (ω * ∫ r in (2 * D)..(max (2 * D) R),
      r ^ ((d : ℝ) - 1 - ((d : ℝ) / 2 + θ))) ≤ ENNReal.ofReal (ω * (2 ^ θ * (5 ^ θ / θ))) := by
    rw [hI4, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmax5 : max (2 * D) R ≤ 5 := max_le (by linarith) (by linarith)
    have hm0 : 0 ≤ max (2 * D) R := le_max_of_le_left (by linarith)
    have h5 : (max (2 * D) R) ^ θ ≤ 5 ^ θ := Real.rpow_le_rpow hm0 hmax5 hθ0.le
    have h6 : 0 ≤ (2 * D) ^ θ := Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) ≤ 2 ^ θ := Real.rpow_nonneg (by norm_num) _
    calc 2 ^ θ * (ω * (((max (2 * D) R) ^ θ - (2 * D) ^ θ) / θ)) ≤ 2 ^ θ * (ω * (5 ^ θ / θ)) := by
          gcongr
          linarith
      _ = ω * (2 ^ θ * (5 ^ θ / θ)) := by ring
  calc _ ≤ ENNReal.ofReal (ω * (1 / ((d : ℝ) / 2))) + ENNReal.ofReal (ω * (1 / ((d : ℝ) - θ))) +
        ENNReal.ofReal (ω * (4 ^ d / d)) + ENNReal.ofReal (ω * (2 ^ θ * (5 ^ θ / θ))) :=
        add_le_add (add_le_add (add_le_add t1 t2) t3) t4
    _ = ENNReal.ofReal (ω * (1 / ((d : ℝ) / 2) + 1 / ((d : ℝ) - θ) + 4 ^ d / d + 2 ^ θ * (5 ^ θ / θ))) := by
        have p1 : 0 ≤ ω * (1 / ((d : ℝ) / 2)) := by positivity
        have p2 : 0 ≤ ω * (1 / ((d : ℝ) - θ)) := mul_nonneg hω0 (by
          have : 0 < (d : ℝ) - θ := by rw [hθ]; linarith
          positivity)
        have p3 : 0 ≤ ω * (4 ^ d / d) := by positivity
        have p4 : 0 ≤ ω * (2 ^ θ * (5 ^ θ / θ)) := by positivity
        rw [← ENNReal.ofReal_add p1 p2, ← ENNReal.ofReal_add (add_nonneg p1 p2) p3,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg p1 p2) p3) p4]
        congr 1; ring

end HRS.MS.R26T8A
