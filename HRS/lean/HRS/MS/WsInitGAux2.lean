import HRS.MS.WsInitGAux1

/-!
# S21 packet G, part 2: time regularity of `D^j G(τ)(x) v` and the double integration by parts against a cosine

* `s21g_hasDerivWithin_iter`: from `S21GDiff` (and `C_b^J` membership) the real function `τ ↦ D^j (G τ) x v` has derivative
  `D^j (G' τ) x v` within `[0,T]`.
* `s21g_norm_iter_le_cb`: `‖D^j g x‖ ≤ cbNorm J g` for `g ∈ C_b^J`, `j ≤ J`.
* `s21g_cos_ibp`: for `u0' = u1`, `u1' = u2` on `[0,T]` (one-sided at the endpoints), `u2` continuous, and `sin(omT) = 0`:
  `|∫_0^T cos(omt) u0(t) dt| ≤ om^{-2} (2B + T B)` when `|u1(0)|, |u1(T)|, |u2| ≤ B`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ}

theorem s21g_norm_iter_le_cb {J j : ℕ} {g : Euc d → ℝ} (h : MemCb J g) (hj : j ≤ J) (x : Euc d) :
    ‖iteratedFDeriv ℝ j g x‖ ≤ cbNorm J g := by
  unfold cbNorm
  have h0 : ‖iteratedFDeriv ℝ j g x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j g z‖ :=
    le_ciSup (h.2 j hj) x
  refine h0.trans ?_
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j g z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem s21g_abs_iter_le_cb {J j : ℕ} {g : Euc d → ℝ} (h : MemCb J g) (hj : j ≤ J) (x : Euc d)
    (v : Fin j → Euc d) :
    |iteratedFDeriv ℝ j g x v| ≤ cbNorm J g * ∏ i, ‖v i‖ := by
  have h1 := (iteratedFDeriv ℝ j g x).le_opNorm v
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_right (s21g_norm_iter_le_cb h hj x) (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- The iterated derivative of the difference quotient, evaluated. -/
theorem s21g_iter_quot {J j : ℕ} (hj : j ≤ J) {g1 g2 g' : Euc d → ℝ} (h1 : MemCb J g1) (h2 : MemCb J g2)
    (h3 : MemCb J g') (a : ℝ) (x : Euc d) (v : Fin j → Euc d) :
    iteratedFDeriv ℝ j (fun y => a * (g1 y - g2 y) - g' y) x v =
      a * (iteratedFDeriv ℝ j g1 x v - iteratedFDeriv ℝ j g2 x v) - iteratedFDeriv ℝ j g' x v := by
  have c1 : ContDiffAt ℝ (j : WithTop ℕ∞) g1 x := (h1.1.of_le (by exact_mod_cast hj)).contDiffAt
  have c2 : ContDiffAt ℝ (j : WithTop ℕ∞) g2 x := (h2.1.of_le (by exact_mod_cast hj)).contDiffAt
  have c3 : ContDiffAt ℝ (j : WithTop ℕ∞) g' x := (h3.1.of_le (by exact_mod_cast hj)).contDiffAt
  have e : (fun y => a * (g1 y - g2 y) - g' y) = (a • (g1 - g2)) - g' := by
    funext y; simp [smul_eq_mul]
  have hd : ContDiffAt ℝ (j : WithTop ℕ∞) (g1 - g2) x := c1.sub c2
  have hs : ContDiffAt ℝ (j : WithTop ℕ∞) (a • (g1 - g2)) x := hd.const_smul a
  rw [e, iteratedFDeriv_sub_apply hs c3, iteratedFDeriv_const_smul_apply hd,
    iteratedFDeriv_sub_apply c1 c2]
  simp [smul_eq_mul]

/-- **Time derivative of a derivative coordinate.** -/
theorem s21g_hasDerivWithin_iter {J : ℕ} {T : ℝ} {G G' : ℝ → Euc d → ℝ}
    (hG : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G τ)) (hG' : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemCb J (G' τ))
    (hD : S21GDiff J T G G') {j : ℕ} (hj : j ≤ J) (x : Euc d) (v : Fin j → Euc d) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => iteratedFDeriv ℝ j (G t) x v) (iteratedFDeriv ℝ j (G' τ) x v)
      (Set.Icc (0 : ℝ) T) τ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set P : ℝ := ∏ i, ‖v i‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
  obtain ⟨δ, hδ, hδ'⟩ := hD τ hτ (ε / (2 * (P + 1))) (by positivity)
  refine ⟨δ, hδ, fun y hy hdy => ?_⟩
  obtain ⟨hyI, hyne⟩ := hy
  have hyne' : y - τ ≠ 0 := sub_ne_zero.2 hyne
  rw [Real.dist_eq] at hdy
  have hdy' : |y - τ| < δ := hdy
  have hmem : τ + (y - τ) ∈ Set.Icc (0 : ℝ) T := by rw [add_sub_cancel]; exact hyI
  have hb := hδ' (y - τ) hyne' hdy' hmem j hj x
  rw [add_sub_cancel] at hb
  have hq := s21g_iter_quot hj (hG y hyI) (hG τ hτ) (hG' τ hτ) (y - τ)⁻¹ x v
  have hq2 : |iteratedFDeriv ℝ j (fun z => (y - τ)⁻¹ * (G y z - G τ z) - G' τ z) x v| ≤
      ε / (2 * (P + 1)) * P := by
    have h1 := (iteratedFDeriv ℝ j (fun z => (y - τ)⁻¹ * (G y z - G τ z) - G' τ z) x).le_opNorm v
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hb hP0)
  rw [hq] at hq2
  rw [Real.dist_eq]
  have e : slope (fun t => iteratedFDeriv ℝ j (G t) x v) τ y - iteratedFDeriv ℝ j (G' τ) x v =
      (y - τ)⁻¹ * (iteratedFDeriv ℝ j (G y) x v - iteratedFDeriv ℝ j (G τ) x v) -
        iteratedFDeriv ℝ j (G' τ) x v := by
    rw [slope_def_field]; ring
  rw [e]
  refine lt_of_le_of_lt hq2 ?_
  have : ε / (2 * (P + 1)) * P ≤ ε / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- Double integration by parts against `cos(om t)`. -/
theorem s21g_cos_ibp {T om : ℝ} (hT : 0 ≤ T) (hom : 0 < om) (hsin : Real.sin (om * T) = 0)
    {u0 u1 u2 : ℝ → ℝ}
    (hd0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u0 (u1 τ) (Set.Icc (0 : ℝ) T) τ)
    (hd1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u1 (u2 τ) (Set.Icc (0 : ℝ) T) τ)
    (hc2 : ContinuousOn u2 (Set.Icc (0 : ℝ) T)) {B : ℝ} (h1a : |u1 0| ≤ B) (h1b : |u1 T| ≤ B)
    (h2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, |u2 τ| ≤ B) :
    |∫ t in (0 : ℝ)..T, Real.cos (om * t) * u0 t| ≤ om⁻¹ ^ 2 * (2 * B + T * B) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans h1a
  have hc0 : ContinuousOn u0 (Set.Icc (0 : ℝ) T) := fun τ hτ => (hd0 τ hτ).continuousWithinAt
  have hc1 : ContinuousOn u1 (Set.Icc (0 : ℝ) T) := fun τ hτ => (hd1 τ hτ).continuousWithinAt
  have hIcc : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le hT
  have hc0' : ContinuousOn u0 (Set.uIcc (0 : ℝ) T) := by rw [hIcc]; exact hc0
  have hc1' : ContinuousOn u1 (Set.uIcc (0 : ℝ) T) := by rw [hIcc]; exact hc1
  have hc2' : ContinuousOn u2 (Set.uIcc (0 : ℝ) T) := by rw [hIcc]; exact hc2
  have hmin : min (0 : ℝ) T = 0 := min_eq_left hT
  have hmax : max (0 : ℝ) T = T := max_eq_right hT
  -- derivative at interior points
  have hint : ∀ {u u' : ℝ → ℝ}, (∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt u (u' τ) (Set.Icc (0 : ℝ) T) τ) →
      ∀ τ ∈ Set.Ioo (min (0 : ℝ) T) (max (0 : ℝ) T), HasDerivWithinAt u (u' τ) (Set.Ioi τ) τ := by
    intro u u' h τ hτ
    rw [hmin, hmax] at hτ
    have h1 := h τ ⟨hτ.1.le, hτ.2.le⟩
    exact (h1.hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)).hasDerivWithinAt
  have hs : ∀ t : ℝ, HasDerivAt (fun t => Real.sin (om * t) / om) (Real.cos (om * t)) t := by
    intro t
    have := ((Real.hasDerivAt_sin (om * t)).comp t ((hasDerivAt_id t).const_mul om)).div_const om
    exact this.congr_deriv (by field_simp)
  have hc : ∀ t : ℝ, HasDerivAt (fun t => -(Real.cos (om * t)) / om) (Real.sin (om * t)) t := by
    intro t
    have := ((Real.hasDerivAt_cos (om * t)).comp t ((hasDerivAt_id t).const_mul om)).neg.div_const om
    exact this.congr_deriv (by field_simp)
  have hsc : Continuous fun t : ℝ => Real.sin (om * t) / om := by fun_prop
  have hcc : Continuous fun t : ℝ => -(Real.cos (om * t)) / om := by fun_prop
  have hcosc : Continuous fun t : ℝ => Real.cos (om * t) := by fun_prop
  have hsinc : Continuous fun t : ℝ => Real.sin (om * t) := by fun_prop
  -- step 1
  have step1 : ∫ t in (0 : ℝ)..T, (Real.cos (om * t) * u0 t + Real.sin (om * t) / om * u1 t) = 0 := by
    have := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right (a := 0) (b := T)
      (u := fun t => Real.sin (om * t) / om) (v := u0) (u' := fun t => Real.cos (om * t)) (v' := u1)
      hsc.continuousOn hc0'
      (fun τ _ => (hs τ).hasDerivWithinAt) (hint hd0)
      (hcosc.intervalIntegrable _ _) hc1'.intervalIntegrable
    simpa [hsin] using this
  -- step 2
  have step2 : ∫ t in (0 : ℝ)..T, (Real.sin (om * t) * u1 t + -(Real.cos (om * t)) / om * u2 t) =
      (-(Real.cos (om * T)) / om * u1 T - -(Real.cos (om * 0)) / om * u1 0) := by
    exact intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right (a := 0) (b := T)
      (u := fun t => -(Real.cos (om * t)) / om) (v := u1) (u' := fun t => Real.sin (om * t)) (v' := u2)
      hcc.continuousOn hc1'
      (fun τ _ => (hc τ).hasDerivWithinAt) (hint hd1)
      (hsinc.intervalIntegrable _ _) hc2'.intervalIntegrable
  have i0 : IntervalIntegrable (fun t => Real.cos (om * t) * u0 t) volume 0 T :=
    (hcosc.continuousOn.mul hc0').intervalIntegrable
  have i1 : IntervalIntegrable (fun t => Real.sin (om * t) / om * u1 t) volume 0 T :=
    (hsc.continuousOn.mul hc1').intervalIntegrable
  have i2 : IntervalIntegrable (fun t => Real.sin (om * t) * u1 t) volume 0 T :=
    (hsinc.continuousOn.mul hc1').intervalIntegrable
  have i3 : IntervalIntegrable (fun t => -(Real.cos (om * t)) / om * u2 t) volume 0 T :=
    (hcc.continuousOn.mul hc2').intervalIntegrable
  rw [intervalIntegral.integral_add i0 i1] at step1
  rw [intervalIntegral.integral_add i2 i3] at step2
  have e1 : ∫ t in (0 : ℝ)..T, Real.sin (om * t) / om * u1 t = om⁻¹ * ∫ t in (0 : ℝ)..T, Real.sin (om * t) * u1 t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  have e2 : ∫ t in (0 : ℝ)..T, -(Real.cos (om * t)) / om * u2 t =
      -(om⁻¹ * ∫ t in (0 : ℝ)..T, Real.cos (om * t) * u2 t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1; funext t; ring
  rw [e1] at step1
  rw [e2] at step2
  have hI0 : ∫ t in (0 : ℝ)..T, Real.cos (om * t) * u0 t = -(om⁻¹ * ∫ t in (0 : ℝ)..T, Real.sin (om * t) * u1 t) := by
    linarith
  -- bounds
  have hI2 : |∫ t in (0 : ℝ)..T, Real.cos (om * t) * u2 t| ≤ T * B := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T)
      (f := fun t => Real.cos (om * t) * u2 t) (C := B) (fun t ht => by
        rw [Set.uIoc_of_le hT] at ht
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.cos (om * t)| * |u2 t| ≤ 1 * B :=
              mul_le_mul (Real.abs_cos_le_one _) (h2 t ⟨ht.1.le, ht.2⟩) (abs_nonneg _) zero_le_one
          _ = B := one_mul _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at this
    exact this.trans (by rw [mul_comm])
  have hsol : ∫ t in (0 : ℝ)..T, Real.sin (om * t) * u1 t =
      om⁻¹ * (∫ t in (0 : ℝ)..T, Real.cos (om * t) * u2 t) +
        (-(Real.cos (om * T)) / om * u1 T - -(Real.cos (om * 0)) / om * u1 0) := by
    linarith
  have hcT : |Real.cos (om * T)| ≤ 1 := Real.abs_cos_le_one _
  have hw : 0 < om⁻¹ := inv_pos.2 hom
  have hbd : |∫ t in (0 : ℝ)..T, Real.sin (om * t) * u1 t| ≤ om⁻¹ * (T * B) + om⁻¹ * (2 * B) := by
    rw [hsol]
    have e3 : -(Real.cos (om * T)) / om * u1 T - -(Real.cos (om * 0)) / om * u1 0 =
        om⁻¹ * (-(Real.cos (om * T)) * u1 T + Real.cos (om * 0) * u1 0) := by ring
    have h4 : |-(Real.cos (om * T)) * u1 T + Real.cos (om * 0) * u1 0| ≤ 2 * B := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg]
      have hc0'' : |Real.cos (om * 0)| ≤ 1 := Real.abs_cos_le_one _
      nlinarith [mul_le_mul hcT h1b (abs_nonneg _) zero_le_one,
        mul_le_mul hc0'' h1a (abs_nonneg _) zero_le_one]
    have h5 : |om⁻¹ * ∫ t in (0 : ℝ)..T, Real.cos (om * t) * u2 t| ≤ om⁻¹ * (T * B) := by
      rw [abs_mul, abs_of_pos hw]
      exact mul_le_mul_of_nonneg_left hI2 hw.le
    have h6 : |om⁻¹ * (-(Real.cos (om * T)) * u1 T + Real.cos (om * 0) * u1 0)| ≤ om⁻¹ * (2 * B) := by
      rw [abs_mul, abs_of_pos hw]
      exact mul_le_mul_of_nonneg_left h4 hw.le
    rw [e3]
    exact (abs_add_le _ _).trans (add_le_add h5 h6)
  rw [hI0, abs_neg, abs_mul, abs_of_pos (inv_pos.2 hom)]
  calc om⁻¹ * |∫ t in (0 : ℝ)..T, Real.sin (om * t) * u1 t| ≤ om⁻¹ * (om⁻¹ * (T * B) + om⁻¹ * (2 * B)) :=
        mul_le_mul_of_nonneg_left hbd (inv_pos.2 hom).le
    _ = om⁻¹ ^ 2 * (2 * B + T * B) := by ring

end HRS.MS.S21
