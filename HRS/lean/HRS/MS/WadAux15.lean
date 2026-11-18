import HRS.MS.WadAux14

/-!
# S8.3, packet D5'' (Route A): the singular Beta-type kernel estimate behind the Gronwall step

The a priori estimate for a classical backward solution closes through the exponentially weighted
bound `‖∇w_r‖ ≤ Θ e^{λ(t-r)} (t-r)^{-3/4}`.  The key quantitative input is the kernel inequality
`s84_kernel`: for every `T, ε > 0` there is `λ > 0` such that for `0 < t - r ≤ T`
`∫_r^t (s-r)^{-3/4} (t-s)^{-3/4} e^{λ(t-s)} ds ≤ ε e^{λ(t-r)} (t-r)^{-3/4}`.
Proof: split at the midpoint; the half near `t` gains `e^{-λτ/2}`, the half near `r` gains `λ^{-1/8}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.Wad

/-- `y^p ≤ e^y` for `y > 0`, `0 ≤ p ≤ 1`. -/
theorem s84_rpow_le_exp {y p : ℝ} (hy : 0 < y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : y ^ p ≤ Real.exp y := by
  have h1 : y ^ p ≤ 1 + y := by
    by_cases hy1 : y ≤ 1
    · have := Real.rpow_le_one hy.le hy1 hp0
      linarith
    · push Not at hy1
      have := Real.rpow_le_rpow_of_exponent_le hy1.le hp1
      rw [Real.rpow_one] at this
      linarith
  exact h1.trans (by linarith [Real.add_one_le_exp y])

/-- `e^{-y} ≤ y^{-p}` for `y > 0`, `0 ≤ p ≤ 1`. -/
theorem s84_exp_neg_le {y p : ℝ} (hy : 0 < y) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.exp (-y) ≤ y ^ (-p) := by
  have h := s84_rpow_le_exp hy hp0 hp1
  rw [Real.rpow_neg hy.le, Real.exp_neg]
  exact inv_anti₀ (Real.rpow_pos_of_pos hy p) h

/-- `∫_0^h u^{-3/4} e^{-λu} du ≤ 8 h^{1/8} λ^{-1/8}`. -/
theorem s84_int_small {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h) :
    ∫ u in (0 : ℝ)..h, u ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * u)) ≤
      8 * h ^ (1 / 8 : ℝ) * lam ^ (-(1 / 8 : ℝ)) := by
  have hint1 : IntervalIntegrable (fun u : ℝ => u ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * u)))
      MeasureTheory.volume 0 h := by
    refine IntervalIntegrable.mul_continuousOn
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)) ?_
    exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-(lam * u))).continuousOn
  have hint2 : IntervalIntegrable (fun u : ℝ => lam ^ (-(1 / 8 : ℝ)) * u ^ (-(7 / 8 : ℝ)))
      MeasureTheory.volume 0 h :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hmono : ∫ u in (0 : ℝ)..h, u ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * u)) ≤
      ∫ u in (0 : ℝ)..h, lam ^ (-(1 / 8 : ℝ)) * u ^ (-(7 / 8 : ℝ)) := by
    refine intervalIntegral.integral_mono_on hh.le hint1 hint2 fun u hu => ?_
    rcases hu.1.eq_or_lt with h0 | h0
    · subst h0
      simp [Real.zero_rpow]
    · have hlu : 0 < lam * u := mul_pos hlam h0
      have h1 := s84_exp_neg_le hlu (p := 1 / 8) (by norm_num) (by norm_num)
      calc u ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * u))
          ≤ u ^ (-(3 / 4 : ℝ)) * (lam * u) ^ (-(1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg h0.le _)
        _ = lam ^ (-(1 / 8 : ℝ)) * u ^ (-(7 / 8 : ℝ)) := by
            rw [Real.mul_rpow hlam.le h0.le, mul_left_comm, ← Real.rpow_add h0]
            norm_num
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  have e1 : (-(7 / 8 : ℝ) + 1) = 1 / 8 := by norm_num
  rw [e1, Real.zero_rpow (by norm_num)]
  ring

/-- `∫_0^h u^{-3/4} du = 4 h^{1/4}`. -/
theorem s84_int_rpow {h : ℝ} :
    ∫ u in (0 : ℝ)..h, u ^ (-(3 / 4 : ℝ)) = 4 * h ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have e1 : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  rw [e1, Real.zero_rpow (by norm_num)]
  ring

/-- **Kernel inequality.** -/
theorem s84_kernel {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ r t : ℝ, r < t → t - r ≤ T →
      ∫ s in r..t, (s - r) ^ (-(3 / 4 : ℝ)) *
          ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))) ≤
        ε * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ))) := by
  -- choose `κ ≥ 1` large and `λ = κ⁸`
  set Cc : ℝ := 2 * (8 * (T + 1) + 4) with hCc
  have hCc0 : 0 < Cc := by positivity
  obtain ⟨κ, hκ1, hκ⟩ : ∃ κ : ℝ, 1 ≤ κ ∧ Cc / ε ≤ κ :=
    ⟨max 1 (Cc / ε), le_max_left _ _, le_max_right _ _⟩
  have hκ0 : 0 < κ := by linarith
  refine ⟨κ ^ 8, by positivity, fun r t hrt hT' => ?_⟩
  set lam : ℝ := κ ^ 8 with hlam
  have hlam0 : 0 < lam := by positivity
  set τ : ℝ := t - r with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  set m : ℝ := r + τ / 2 with hm
  have hrm : r < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm, hτ]; linarith
  have htm : t - m = τ / 2 := by rw [hm, hτ]; ring
  have hmr : m - r = τ / 2 := by rw [hm]; ring
  have hτ2 : 0 < τ / 2 := by positivity
  -- integrability
  have hI1 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) MeasureTheory.volume r m := by
    have h1 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume r m := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m - r) (r := -(3 / 4 : ℝ))
        (by norm_num)).comp_sub_right r
      simpa using this
    refine h1.mul_continuousOn ?_
    refine ContinuousOn.mul ?_ (by fun_prop : Continuous fun s : ℝ => Real.exp (lam * (t - s))).continuousOn
    refine ContinuousOn.rpow_const (by fun_prop) fun s hs => Or.inl ?_
    rw [Set.uIcc_of_le hrm.le] at hs
    have : s ≤ m := hs.2
    have : t - s ≥ τ / 2 := by linarith
    exact ne_of_gt (by linarith)
  have hI2 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) MeasureTheory.volume m t := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))
        MeasureTheory.volume m t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - m) (r := -(3 / 4 : ℝ))
        (by norm_num)).comp_sub_left t
      have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume m t := by
        simpa using this.symm
      exact h2.mul_continuousOn (by fun_prop : Continuous fun s : ℝ => Real.exp (lam * (t - s))).continuousOn
    refine h1.continuousOn_mul ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun s hs => Or.inl ?_
    rw [Set.uIcc_of_le hmt.le] at hs
    have : m ≤ s := hs.1
    have : s - r ≥ τ / 2 := by linarith
    exact ne_of_gt (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  -- first half
  have hA : ∫ s in r..m, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))) ≤
      (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * τ) *
        (8 * (τ / 2) ^ (1 / 8 : ℝ) * lam ^ (-(1 / 8 : ℝ))) := by
    have hg : IntervalIntegrable (fun s : ℝ => (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * τ) *
        ((s - r) ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * (s - r))))) MeasureTheory.volume r m := by
      have h1 : IntervalIntegrable (fun s : ℝ => (s - r) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume r m := by
        have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m - r) (r := -(3 / 4 : ℝ))
          (by norm_num)).comp_sub_right r
        simpa using this
      exact (h1.mul_continuousOn
        (by fun_prop : Continuous fun s : ℝ => Real.exp (-(lam * (s - r)))).continuousOn).const_mul _
    have hmono := intervalIntegral.integral_mono_on hrm.le hI1 hg (fun s hs => by
      rcases hs.1.eq_or_lt with h0 | h0
      · subst h0
        simp [Real.zero_rpow]
      · have h1 : (τ / 2) ≤ t - s := by
          have := hs.2
          linarith
        have h2 : (t - s) ^ (-(3 / 4 : ℝ)) ≤ (τ / 2) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hτ2 h1 (by norm_num)
        have h3 : Real.exp (lam * (t - s)) = Real.exp (lam * τ) * Real.exp (-(lam * (s - r))) := by
          rw [← Real.exp_add]; congr 1; rw [hτ]; ring
        have h4 : 0 ≤ (s - r) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith [h0]) _
        calc (s - r) ^ (-(3 / 4 : ℝ)) * ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))
            ≤ (s - r) ^ (-(3 / 4 : ℝ)) * ((τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) h4
          _ = (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * τ) *
              ((s - r) ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * (s - r)))) := by
              rw [h3]; ring)
    have hC0 : 0 ≤ (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * τ) :=
      mul_nonneg (Real.rpow_nonneg hτ2.le _) (Real.exp_pos _).le
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have := intervalIntegral.integral_comp_sub_right (a := r) (b := m)
      (fun u : ℝ => u ^ (-(3 / 4 : ℝ)) * Real.exp (-(lam * u))) r
    simp only [sub_self, hmr] at this
    rw [this]
    exact s84_int_small hlam0 hτ2
  -- second half
  have hB : ∫ s in m..t, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))) ≤
      (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (τ / 2)) * (4 * (τ / 2) ^ (1 / 4 : ℝ)) := by
    have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume m t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - m) (r := -(3 / 4 : ℝ))
        (by norm_num)).comp_sub_left t
      simpa using this.symm
    have hg : IntervalIntegrable (fun s : ℝ => (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (τ / 2)) *
        (t - s) ^ (-(3 / 4 : ℝ))) MeasureTheory.volume m t := h2.const_mul _
    have hmono := intervalIntegral.integral_mono_on hmt.le hI2 hg (fun s hs => by
      rcases hs.2.eq_or_lt with h0 | h0
      · subst h0
        simp [Real.zero_rpow]
      · have h1 : (τ / 2) ≤ s - r := by
          have := hs.1
          linarith
        have h2' : (s - r) ^ (-(3 / 4 : ℝ)) ≤ (τ / 2) ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hτ2 h1 (by norm_num)
        have h3 : Real.exp (lam * (t - s)) ≤ Real.exp (lam * (τ / 2)) := by
          apply Real.exp_le_exp.2
          have : t - s ≤ τ / 2 := by have := hs.1; linarith
          nlinarith
        have h4 : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith [h0]) _
        calc (s - r) ^ (-(3 / 4 : ℝ)) * ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))
            = ((s - r) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))) * (t - s) ^ (-(3 / 4 : ℝ)) := by ring
          _ ≤ ((τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (τ / 2))) * (t - s) ^ (-(3 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul h2' h3 (Real.exp_pos _).le
                (Real.rpow_nonneg hτ2.le _)) h4)
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine le_of_eq ?_
    have := intervalIntegral.integral_comp_sub_left (a := m) (b := t)
      (fun u : ℝ => u ^ (-(3 / 4 : ℝ))) t
    simp only [sub_self, htm] at this
    rw [this, s84_int_rpow]
  -- combine
  have hκ8 : lam ^ (1 / 8 : ℝ) = κ := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hκ0.le]; norm_num
  have hlm8 : lam ^ (-(1 / 8 : ℝ)) = κ⁻¹ := by
    rw [Real.rpow_neg hlam0.le, hκ8]
  have hκ4 : lam ^ (1 / 4 : ℝ) = κ ^ 2 := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul hκ0.le]
    rw [← Real.rpow_natCast κ 2]; norm_num
  set P : ℝ := τ ^ (-(3 / 4 : ℝ)) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hτ0 _
  set E : ℝ := Real.exp (lam * τ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hhalf : (τ / 2) ^ (-(3 / 4 : ℝ)) ≤ 2 * P := by
    rw [Real.div_rpow hτ0.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have : (2 : ℝ) ^ (-(-(3 / 4 : ℝ))) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    nlinarith
  have hq8 : (τ / 2) ^ (1 / 8 : ℝ) ≤ T + 1 := by
    have hx : τ / 2 ≤ T := by linarith
    by_cases h1 : τ / 2 ≤ 1
    · have := Real.rpow_le_one hτ2.le h1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
      linarith
    · push Not at h1
      have := Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num : (1 / 8 : ℝ) ≤ 1)
      rw [Real.rpow_one] at this
      linarith
  have hq4 : (τ / 2) ^ (1 / 4 : ℝ) ≤ lam ^ (-(1 / 4 : ℝ)) * Real.exp (lam * (τ / 2)) := by
    have h := s84_rpow_le_exp (mul_pos hlam0 hτ2) (p := 1 / 4) (by norm_num) (by norm_num)
    rw [Real.mul_rpow hlam0.le hτ2.le] at h
    have hl4 : 0 < lam ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlam0 _
    rw [Real.rpow_neg hlam0.le]
    rw [← div_eq_inv_mul, le_div_iff₀ hl4]
    linarith
  have hEh : Real.exp (lam * (τ / 2)) * Real.exp (lam * (τ / 2)) = E := by
    rw [← Real.exp_add, hE]; congr 1; ring
  have hlm4 : lam ^ (-(1 / 4 : ℝ)) = (κ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hlam0.le, hκ4]
  -- bounds A and B
  have hAfin : (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * τ) *
        (8 * (τ / 2) ^ (1 / 8 : ℝ) * lam ^ (-(1 / 8 : ℝ))) ≤ P * E * (16 * (T + 1) / κ) := by
    rw [hlm8, ← hE]
    have h1 : 0 ≤ (τ / 2) ^ (1 / 8 : ℝ) := Real.rpow_nonneg hτ2.le _
    have hκi : 0 ≤ κ⁻¹ := inv_nonneg.2 hκ0.le
    calc (τ / 2) ^ (-(3 / 4 : ℝ)) * E * (8 * (τ / 2) ^ (1 / 8 : ℝ) * κ⁻¹)
        ≤ (2 * P) * E * (8 * (T + 1) * κ⁻¹) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hhalf hE0.le) ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq8 (by norm_num)) hκi
      _ = P * E * (16 * (T + 1) / κ) := by field_simp; ring
  have hBfin : (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (τ / 2)) *
        (4 * (τ / 2) ^ (1 / 4 : ℝ)) ≤ P * E * (8 / κ) := by
    have hκ2 : (κ ^ 2)⁻¹ ≤ κ⁻¹ := by
      apply inv_anti₀ hκ0
      nlinarith
    have h1 : 0 < Real.exp (lam * (τ / 2)) := Real.exp_pos _
    calc (τ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (τ / 2)) * (4 * (τ / 2) ^ (1 / 4 : ℝ))
        ≤ (2 * P) * Real.exp (lam * (τ / 2)) * (4 * (κ⁻¹ * Real.exp (lam * (τ / 2)))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hhalf h1.le) ?_ (by positivity) (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine hq4.trans ?_
          rw [hlm4]
          exact mul_le_mul_of_nonneg_right hκ2 h1.le
      _ = 8 * P * (Real.exp (lam * (τ / 2)) * Real.exp (lam * (τ / 2))) * κ⁻¹ := by ring
      _ = P * E * (8 / κ) := by rw [hEh]; field_simp
  have htot : (16 * (T + 1) / κ) + 8 / κ ≤ ε := by
    rw [← add_div, div_le_iff₀ hκ0]
    have := (div_le_iff₀ hε).1 hκ
    nlinarith
  calc _ ≤ P * E * (16 * (T + 1) / κ) + P * E * (8 / κ) := add_le_add (hA.trans hAfin) (hB.trans hBfin)
    _ = P * E * ((16 * (T + 1) / κ) + 8 / κ) := by ring
    _ ≤ P * E * ε := mul_le_mul_of_nonneg_left htot (by positivity)
    _ = ε * (E * P) := by ring

end HRS.MS.Wad
