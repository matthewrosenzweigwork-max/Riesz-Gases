import HRS.MS.CritForceMom12

/-!
# S8.2 NormalForm packet R03, part 13: the log-weighted row, and the five rows together
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

theorem s82n_E5 (hd : 2 ≤ d) (β M G c : ℝ) (hβ : 0 < β) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : S82nShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 2 *
          (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) ^ 2 *
          Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (C * jbracket x ^ M * s82n_logN N ^ 3) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Mom := s82n_Mom d M G c with hMom
  have hMom0 : 0 ≤ Mom := s82n_Mom_nonneg (by omega) M G c hM hG hc
  set D1 := |Real.log r0| with hD1
  have hD10 : 0 ≤ D1 := abs_nonneg _
  have hB50 := s82n_B5_nonneg (by omega : 1 ≤ d) β c0 r0 hβ hc0 hr0
  refine ⟨4 ^ M * G * κ * s82n_B5 d β c0 r0 +
      (1 + r0 ^ (-s82n_critS d)) ^ 2 * (2 + D1) ^ 2 * Mom, by positivity, ?_⟩
  intro ρ hρ hρG N hN x
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hLe : s82n_logN N = 1 + Real.log N := s82n_logN_eq N hN1
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  set L := s82n_logN N with hL
  have hL1 : 1 ≤ L := by rw [hLe]; linarith
  set A : ℝ := β * c0 / N with hA
  have hApos : 0 < A := by positivity
  set K0 : ℝ := (1 + r0 ^ (-s82n_critS d)) ^ 2 * (L + 1 + D1) ^ 2 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hrow := s82n_row (by omega : 1 ≤ d) M G c r0 K0 hM hG hc hr0 hr1 hK00 ρ hρ hρG x
    (fun y => s82n_pole x y ^ 2 * (L + 1 + |Real.log (s82n_smallRadius x y)|) ^ 2 *
      Real.exp (-(β / N) * q (x - y)))
    (by have := s82n_measurable_smallRadius x; have := hq.measurable
        unfold s82n_pole; fun_prop)
    (fun r => (1 + r ^ (-s82n_critS d)) ^ 2 * (L + 1 + |Real.log r|) ^ 2 *
      Real.exp (-(A * r ^ (-s82n_critS d))))
    (s82n_g5 d L A r0)
    (fun r _ => by positivity) (by fun_prop)
    (s82n_g5_intervalIntegrable hd L A r0 hr0 hApos)
    (fun r hr => s82n_E5_profile hd L A r0 r hApos hr.1 hr.2.le hr1)
    (fun y hy => by
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 2 *
        (L + 1 + |Real.log (s82n_smallRadius x y)|) ^ 2 * Real.exp (-(β / N) * q (x - y)) ≤ _
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
      have hlog : |Real.log (s82n_smallRadius x y)| ≤ D1 := by
        have a1 := Real.log_le_log hr0 h1
        have a2 := Real.log_nonpos ht.le h2
        have a3 := Real.log_nonpos hr0.le hr1
        rw [hD1, abs_of_nonpos a3, abs_of_nonpos a2]; linarith
      show (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ^ 2 *
        (L + 1 + |Real.log (s82n_smallRadius x y)|) ^ 2 * Real.exp (-(β / N) * q (x - y)) ≤ K0
      have hLp : 0 ≤ L + 1 + |Real.log (s82n_smallRadius x y)| := by positivity
      calc _ ≤ (1 + r0 ^ (-s82n_critS d)) ^ 2 * (L + 1 + D1) ^ 2 * 1 := by
            apply mul_le_mul _ hc1 hc2 (by positivity)
            apply mul_le_mul _ _ (by positivity) (by positivity)
            · gcongr
            · gcongr
        _ = K0 := mul_one _)
  refine le_trans (le_of_eq ?_) (hrow.trans ?_)
  · refine lintegral_congr fun y => ?_
    congr 1
    ring
  · refine ENNReal.ofReal_le_ofReal ?_
    have hint := s82n_int_g5_le hd β c0 r0 hβ hc0 hr0 N hN1
    rw [← hL, ← hA] at hint
    have hJ : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s82n_jb_one_le x) hM
    have hP : 0 ≤ 4 ^ M * G * κ := by positivity
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL1
    have hKb : K0 * Mom ≤ (1 + r0 ^ (-s82n_critS d)) ^ 2 * (2 + D1) ^ 2 * Mom * L ^ 3 := by
      have h1 : (L + 1 + D1) ^ 2 ≤ ((2 + D1) * L) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      have h2 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
      have h3 : 0 ≤ (1 + r0 ^ (-s82n_critS d)) ^ 2 * Mom := by positivity
      calc K0 * Mom = ((1 + r0 ^ (-s82n_critS d)) ^ 2 * Mom) * (L + 1 + D1) ^ 2 := by rw [hK0]; ring
        _ ≤ ((1 + r0 ^ (-s82n_critS d)) ^ 2 * Mom) * (((2 + D1) * L) ^ 2) := by gcongr
        _ = ((1 + r0 ^ (-s82n_critS d)) ^ 2 * (2 + D1) ^ 2 * Mom) * L ^ 2 := by ring
        _ ≤ ((1 + r0 ^ (-s82n_critS d)) ^ 2 * (2 + D1) ^ 2 * Mom) * L ^ 3 := by gcongr
    have hI : 4 ^ M * G * κ * (∫ r in (0 : ℝ)..r0, s82n_g5 d L A r0 r) ≤
        4 ^ M * G * κ * (s82n_B5 d β c0 r0 * L ^ 3) := mul_le_mul_of_nonneg_left hint hP
    calc jbracket x ^ M * (4 ^ M * G * (κ * (∫ r in (0 : ℝ)..r0, s82n_g5 d L A r0 r)) + K0 * Mom)
        = jbracket x ^ M * (4 ^ M * G * κ * (∫ r in (0 : ℝ)..r0, s82n_g5 d L A r0 r) + K0 * Mom) := by ring
      _ ≤ jbracket x ^ M * (4 ^ M * G * κ * (s82n_B5 d β c0 r0 * L ^ 3) +
            (1 + r0 ^ (-s82n_critS d)) ^ 2 * (2 + D1) ^ 2 * Mom * L ^ 3) := by gcongr
      _ = _ := by ring

end HRS.MS.S82N
