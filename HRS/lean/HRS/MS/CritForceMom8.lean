import HRS.MS.CritForceMom7

/-!
# S8.2 NormalForm packet R03, part 8: the fourth-power pole row (cost `N²`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_int_g4 (hd : 2 ≤ d) (r0 A : ℝ) (hr0 : 0 < r0) (hA : 0 < A) :
    ∫ r in (0 : ℝ)..r0, (8 * r ^ (d - 1) + 216 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 3)) =
      8 * (r0 ^ d / d) + 216 * ((1 / (s82n_critS d * 2)) *
        (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2)) := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
    (continuous_pow _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 3)
      volume 0 r0 := s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 2
  rw [intervalIntegral.integral_add (i1.const_mul 8) (i2.const_mul 216),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h3 := s82n_ftc_pow (s82n_critS d) r0 A hs hr0 hA 1
  norm_num at h3
  rw [integral_pow]
  have hd1 : d - 1 + 1 = d := by omega
  have : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    rw [Nat.cast_sub (by omega)]; ring
  rw [hd1, this]
  simp only [zero_pow (by omega : d ≠ 0), sub_zero]
  rw [h3]
  ring

theorem s82n_E4 (hd : 2 ≤ d) (β M G c : ℝ) (hβ : 0 < β) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : S82nShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 4 *
          Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * jbracket x ^ M * (N : ℝ) ^ 2) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Mom := s82n_Mom d M G c with hMom
  have hMom0 : 0 ≤ Mom := s82n_Mom_nonneg (by omega) M G c hM hG hc
  set K0 := (1 + r0 ^ (-s82n_critS d)) ^ 4 with hK0
  set B4 : ℝ := 8 * (r0 ^ d / d) + 108 / s82n_critS d / (β * c0) ^ 2 with hB4
  have hB40 : 0 ≤ B4 := by positivity
  refine ⟨4 ^ M * G * κ * B4 + K0 * Mom, by positivity, ?_⟩
  intro ρ hρ hρG N hN x
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set A : ℝ := β * c0 / N with hA
  have hApos : 0 < A := by positivity
  have hrow := s82n_row (by omega : 1 ≤ d) M G c r0 K0 hM hG hc hr0 hr1 (by positivity) ρ hρ hρG x
    (fun y => s82n_pole x y ^ 4 * Real.exp (-(β / N) * q (x - y)))
    (by have := s82n_measurable_smallRadius x; have := hq.measurable
        unfold s82n_pole; fun_prop)
    (fun r => (1 + r ^ (-s82n_critS d)) ^ 4 * Real.exp (-(A * r ^ (-s82n_critS d))))
    (fun r => 8 * r ^ (d - 1) + 216 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 3))
    (fun r hr => mul_nonneg (by
        have : 0 ≤ r ^ (-s82n_critS d) := Real.rpow_nonneg hr _
        positivity) (Real.exp_pos _).le) (by fun_prop)
    (by
      have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
        (continuous_pow _).intervalIntegrable _ _
      exact (i1.const_mul 8).add
        ((s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hApos 2).const_mul 216))
    (fun r hr => s82n_E4_profile hd A r hApos hr.1)
    (fun y hy => by
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 4 * Real.exp (-(β / N) * q (x - y)) ≤ _
      rw [s82n_smallRadius_near x y (lt_of_lt_of_le hy hr1)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact s82n_cut_near hq.nonneg r0 c0 (fun z h1 h2 => (hnear z h1 h2).1) β hβ N hN1 hs
        (x - y) hy.le)
    (fun y hy => by
      obtain ⟨h1, h2⟩ := s82n_smallRadius_far x y r0 hr0 hr1 hy
      have ht : 0 < s82n_smallRadius x y := lt_of_lt_of_le hr0 h1
      have h5 : s82n_smallRadius x y ^ (-s82n_critS d) ≤ r0 ^ (-s82n_critS d) :=
        s82n_rpow_neg_anti _ r0 _ hs.le hr0 h1
      have h6 : 0 ≤ s82n_smallRadius x y ^ (-s82n_critS d) := Real.rpow_nonneg ht.le _
      have hc1 := s82n_cut_le_one hq.nonneg β hβ N (x - y)
      have hc2 : 0 ≤ Real.exp (-(β / N) * q (x - y)) := (Real.exp_pos _).le
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 4 * Real.exp (-(β / N) * q (x - y)) ≤ K0
      calc _ ≤ (1 + r0 ^ (-s82n_critS d)) ^ 4 * 1 := by
            apply mul_le_mul _ hc1 hc2 (by positivity); gcongr
        _ = K0 := mul_one _)
  refine le_trans (le_of_eq ?_) (hrow.trans ?_)
  · refine lintegral_congr fun y => ?_
    rw [mul_assoc]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [s82n_int_g4 hd r0 A hr0 hApos]
    have hJ : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s82n_jb_one_le x) hM
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hNr
    have hr0s : 0 < r0 ^ s82n_critS d := Real.rpow_pos_of_pos hr0 _
    -- the integral is at most `B4 N²`
    have hint : 8 * (r0 ^ d / d) + 216 * (1 / (s82n_critS d * 2) *
        (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2)) ≤ B4 * (N : ℝ) ^ 2 := by
      have h1 : 1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2 ≤ 1 / A ^ 2 := by
        have : 0 < 1 / (r0 ^ s82n_critS d + A) ^ 2 := by positivity
        linarith
      have h2 : 216 * (1 / (s82n_critS d * 2) * (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2)) ≤
          108 / s82n_critS d / (β * c0) ^ 2 * (N : ℝ) ^ 2 := by
        have hA2 : 1 / A ^ 2 = (N : ℝ) ^ 2 / (β * c0) ^ 2 := by rw [hA]; field_simp
        calc _ ≤ 216 * (1 / (s82n_critS d * 2) * (1 / A ^ 2)) := by gcongr
          _ = _ := by rw [hA2]; field_simp; ring
      have h3 : 8 * (r0 ^ d / d) ≤ 8 * (r0 ^ d / d) * (N : ℝ) ^ 2 := by
        have : 0 ≤ 8 * (r0 ^ d / d) := by positivity
        nlinarith
      rw [hB4]; nlinarith
    have hP : 0 ≤ 4 ^ M * G * κ := by positivity
    have hKM : 0 ≤ K0 * Mom := by positivity
    have h4 : 4 ^ M * G * κ * (8 * (r0 ^ d / d) + 216 * (1 / (s82n_critS d * 2) *
        (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2))) + K0 * Mom ≤
        (4 ^ M * G * κ * B4 + K0 * Mom) * (N : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hint hP, mul_nonneg hKM (sub_nonneg.2 hN2)]
    calc jbracket x ^ M * (4 ^ M * G * (κ * (8 * (r0 ^ d / d) + 216 * (1 / (s82n_critS d * 2) *
          (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2)))) + K0 * Mom)
        = jbracket x ^ M * (4 ^ M * G * κ * (8 * (r0 ^ d / d) + 216 * (1 / (s82n_critS d * 2) *
          (1 / A ^ 2 - 1 / (r0 ^ s82n_critS d + A) ^ 2))) + K0 * Mom) := by ring
      _ ≤ jbracket x ^ M * ((4 ^ M * G * κ * B4 + K0 * Mom) * (N : ℝ) ^ 2) := by gcongr
      _ = _ := by ring

end HRS.MS.S82N
