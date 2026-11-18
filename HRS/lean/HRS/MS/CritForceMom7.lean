import HRS.MS.CritForceMom6

/-!
# S8.2 NormalForm packet R03, part 7: the squared-pole row (cost `log (eN)`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

/-- Repulsion cutoff, near the pole. -/
lemma s82n_cut_near {q : Euc d → ℝ} (hq0 : ∀ z, 0 ≤ q z) (r0 c0 : ℝ)
    (hlow : ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ r0 → c0 * ‖z‖ ^ (-s82n_critS d) ≤ q z)
    (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N) (hs : 0 < s82n_critS d) (z : Euc d) (hz : ‖z‖ ≤ r0) :
    Real.exp (-(β / N) * q z) ≤ Real.exp (-(β * c0 / N * ‖z‖ ^ (-s82n_critS d))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · rw [← h, Real.zero_rpow (by linarith), mul_zero, neg_zero, Real.exp_zero, Real.exp_le_one_iff]
    have : 0 ≤ β / N * q z := mul_nonneg (by positivity) (hq0 z)
    linarith
  · refine Real.exp_le_exp.2 ?_
    have := hlow z h hz
    have h2 : β / N * (c0 * ‖z‖ ^ (-s82n_critS d)) ≤ β / N * q z :=
      mul_le_mul_of_nonneg_left this (by positivity)
    have e : β * c0 / N * ‖z‖ ^ (-s82n_critS d) = β / N * (c0 * ‖z‖ ^ (-s82n_critS d)) := by ring
    rw [e]; linarith

lemma s82n_cut_le_one {q : Euc d → ℝ} (hq0 : ∀ z, 0 ≤ q z) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    (z : Euc d) : Real.exp (-(β / N) * q z) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ β / N * q z := mul_nonneg (by positivity) (hq0 z)
  linarith

lemma s82n_logN_eq (N : ℕ) (hN : 1 ≤ N) : s82n_logN N = 1 + Real.log N := by
  have : (0 : ℝ) < N := by exact_mod_cast hN
  unfold s82n_logN
  rw [Real.log_mul (Real.exp_pos 1).ne' this.ne', Real.log_exp]

lemma s82n_log_bound (s r0 b : ℝ) (N : ℕ) (hN : 1 ≤ N) (hs : 0 < s) (hr0 : 0 < r0) (hb : 0 < b) :
    Real.log (r0 ^ s + b / N) - Real.log (b / N) ≤ Real.log N + Real.log (1 + r0 ^ s / b) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr : 0 < r0 ^ s := Real.rpow_pos_of_pos hr0 _
  have hA : 0 < b / N := by positivity
  rw [← Real.log_div (by positivity) hA.ne', ← Real.log_mul hN0.ne' (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have : (r0 ^ s + b / N) / (b / N) = r0 ^ s * N / b + 1 := by field_simp
  rw [this]
  have : (N : ℝ) * (1 + r0 ^ s / b) = N + r0 ^ s * N / b := by field_simp
  rw [this]; linarith

lemma s82n_int_g3 (hd : 2 ≤ d) (r0 A : ℝ) (hr0 : 0 < r0) (hA : 0 < A) :
    ∫ r in (0 : ℝ)..r0, (2 * r ^ (d - 1) + 2 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1)) =
      2 * (r0 ^ d / d) + 2 * ((Real.log (r0 ^ s82n_critS d + A) - Real.log A) / s82n_critS d) := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
    (continuous_pow _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1)
      volume 0 r0 := by
    simpa using s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hA 0
  rw [intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    s82n_ftc_log _ r0 A hs hr0 hA, integral_pow]
  have hd1 : d - 1 + 1 = d := by omega
  have : ((d - 1 : ℕ) : ℝ) + 1 = d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    rw [Nat.cast_sub (by omega)]; ring
  rw [hd1, this]
  simp [zero_pow (by omega : d ≠ 0)]

theorem s82n_E3 (hd : 2 ≤ d) (β M G c : ℝ) (hβ : 0 < β) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : S82nShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 2 *
          Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * jbracket x ^ M * s82n_logN N) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Mom := s82n_Mom d M G c with hMom
  have hMom0 : 0 ≤ Mom := s82n_Mom_nonneg (by omega) M G c hM hG hc
  set B0 := Real.log (1 + r0 ^ s82n_critS d / (β * c0)) with hB0
  have hr0s : 0 < r0 ^ s82n_critS d := Real.rpow_pos_of_pos hr0 _
  have hB00 : 0 ≤ B0 := by
    have : 0 ≤ r0 ^ s82n_critS d / (β * c0) := by positivity
    exact Real.log_nonneg (by linarith)
  set K0 := (1 + r0 ^ (-s82n_critS d)) ^ 2 with hK0
  set B3 : ℝ := 2 * (r0 ^ d / d) + (2 / s82n_critS d) * (B0 + 1) with hB3
  have hB30 : 0 ≤ B3 := by positivity
  refine ⟨4 ^ M * G * κ * B3 + K0 * Mom, by positivity, ?_⟩
  intro ρ hρ hρG N hN x
  have hN1 : 1 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set A : ℝ := β * c0 / N with hA
  have hApos : 0 < A := by positivity
  have hrow := s82n_row (by omega : 1 ≤ d) M G c r0 K0 hM hG hc hr0 hr1 (sq_nonneg _) ρ hρ hρG x
    (fun y => s82n_pole x y ^ 2 * Real.exp (-(β / N) * q (x - y)))
    (by have := s82n_measurable_smallRadius x; have := hq.measurable
        unfold s82n_pole; fun_prop)
    (fun r => (1 + r ^ (-s82n_critS d)) ^ 2 * Real.exp (-(A * r ^ (-s82n_critS d))))
    (fun r => 2 * r ^ (d - 1) + 2 * (r ^ (s82n_critS d - 1) / (r ^ s82n_critS d + A) ^ 1))
    (fun r _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (by fun_prop)
    (by
      have i1 : IntervalIntegrable (fun r : ℝ => r ^ (d - 1)) volume 0 r0 :=
        (continuous_pow _).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun r : ℝ => r ^ (s82n_critS d - 1) /
          (r ^ s82n_critS d + A) ^ 1) volume 0 r0 := by
        simpa using s82n_integrand_intervalIntegrable (s82n_critS d) r0 A hs hr0 hApos 0
      exact (i1.const_mul 2).add (i2.const_mul 2))
    (fun r hr => s82n_E3_profile hd A r hApos hr.1)
    (fun y hy => by
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 2 * Real.exp (-(β / N) * q (x - y)) ≤ _
      rw [s82n_smallRadius_near x y (lt_of_lt_of_le hy hr1)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
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
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 2 * Real.exp (-(β / N) * q (x - y)) ≤ K0
      calc _ ≤ (1 + r0 ^ (-s82n_critS d)) ^ 2 * 1 := by
            apply mul_le_mul _ hc1 hc2 (sq_nonneg _); gcongr
        _ = K0 := mul_one _)
  refine le_trans (le_of_eq ?_) (hrow.trans ?_)
  · refine lintegral_congr fun y => ?_
    rw [mul_assoc]
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [s82n_int_g3 hd r0 A hr0 hApos]
    have hlog := s82n_log_bound (s82n_critS d) r0 (β * c0) N hN1 hs hr0 (mul_pos hβ hc0)
    have hL : s82n_logN N = 1 + Real.log N := s82n_logN_eq N hN1
    have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hJ : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s82n_jb_one_le x) hM
    set a : ℝ := 2 * (r0 ^ d / d) with ha
    set e : ℝ := 2 / s82n_critS d with he
    have ha0 : 0 ≤ a := by positivity
    have he0 : 0 < e := by positivity
    have h1 : 2 * ((Real.log (r0 ^ s82n_critS d + A) - Real.log A) / s82n_critS d) ≤
        e * (Real.log N + B0) := by
      have : 2 * ((Real.log (r0 ^ s82n_critS d + A) - Real.log A) / s82n_critS d) =
          e * (Real.log (r0 ^ s82n_critS d + A) - Real.log A) := by rw [he]; ring
      rw [this]; exact mul_le_mul_of_nonneg_left hlog he0.le
    have h2 : a + e * (Real.log N + B0) ≤ B3 * (1 + Real.log N) := by
      rw [hB3]; nlinarith [mul_nonneg ha0 hl0, mul_nonneg he0.le hl0, mul_nonneg he0.le hB00,
        mul_nonneg (mul_nonneg he0.le hB00) hl0]
    have hP : 0 ≤ 4 ^ M * G * κ := by positivity
    have hKM : 0 ≤ K0 * Mom := by positivity
    rw [hL]
    have h3 : 4 ^ M * G * κ * (a + 2 * ((Real.log (r0 ^ s82n_critS d + A) - Real.log A) /
        s82n_critS d)) + K0 * Mom ≤ (4 ^ M * G * κ * B3 + K0 * Mom) * (1 + Real.log N) := by
      nlinarith [mul_le_mul_of_nonneg_left (h1.trans' le_rfl |>.trans' (le_refl _)) hP,
        mul_le_mul_of_nonneg_left (add_le_add_left h1 a) hP,
        mul_le_mul_of_nonneg_left h2 hP, mul_nonneg hKM hl0]
    calc jbracket x ^ M * (4 ^ M * G * (κ * (a + 2 * ((Real.log (r0 ^ s82n_critS d + A) -
          Real.log A) / s82n_critS d))) + K0 * Mom)
        = jbracket x ^ M * (4 ^ M * G * κ * (a + 2 * ((Real.log (r0 ^ s82n_critS d + A) -
          Real.log A) / s82n_critS d)) + K0 * Mom) := by ring
      _ ≤ jbracket x ^ M * ((4 ^ M * G * κ * B3 + K0 * Mom) * (1 + Real.log N)) := by gcongr
      _ = _ := by ring

end HRS.MS.S82N
