import HRS.MS.WadAux7

/-!
# S8.3, packet D5' (Route A): the Duhamel (mild) representation of a classical backward solution

Let `w : ℝ → ℝ^d → ℝ` be a classical solution on `[0,t]` of `-∂_r w_r = G_r` with `G_r = L_0 w_r + q_r`
(`L_0 = νΔ - a x·∇`, `q_r = G_r - L_0 w_r` the remainder): `w_r ∈ C²` with bounded `w_r, Dw_r, D²w_r`,
`(r,x) ↦ w_r(x), Dw_r(x), D²w_r(x), G_r(x)` jointly continuous on `[0,t] × ℝ^d`, `|G_r(x)| ≤ B_G (1+|x|)`.
Then for `0 ≤ r ≤ t`
`w_r(x) = (P_{t-r} w_t)(x) + ∫_r^t (P_{s-r} q_s)(x) ds` (`s83_mild_form`).

The proof differentiates `s ↦ (P_{s-r} w_s)(x)`: the derivative of the semigroup parameter is the
Kolmogorov equation (`s83_P_hasDerivAt`), the derivative of the datum is `s83_hasDerivAt_theta`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s83_P_eq_Y (a ν r s : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    s83_P a ν (s - r) f x = ∫ z, f (s83_Y a ν r x z s) ∂(stdGaussian (Euc d)) := rfl

/-- Integrability of `z ↦ f(y_s(z))` for continuous `f` of polynomial growth. -/
theorem s83_int_Y {f : Euc d → ℝ} (hf : Continuous f) {K : ℝ} {p : ℕ}
    (hb : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ p) {a ν r s : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hrs : r ≤ s)
    (x : Euc d) : Integrable (fun z => f (s83_Y a ν r x z s)) (stdGaussian (Euc d)) := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg (f 0)).trans (hb 0)
    simpa using this
  refine s83_int_of_poly (C := K * (1 + ‖x‖ + Real.sqrt (ν / a)) ^ p) (p := p)
    (hf.comp (continuous_const.add (continuous_const_smul _))).aestronglyMeasurable fun z => ?_
  rw [Real.norm_eq_abs]
  refine (hb _).trans ?_
  have := s83_poly_y_le ha hν hrs x z p
  calc K * (1 + ‖s83_Y a ν r x z s‖) ^ p ≤ K * ((1 + ‖x‖ + Real.sqrt (ν / a)) ^ p * (1 + ‖z‖) ^ p) :=
        mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

/-- Bound of `L_0 h` for `h ∈ C²` with bounded derivatives. -/
theorem s83_L0_bound {h : Euc d → ℝ} {B1 B2 : ℝ} (hB1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B1)
    (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) (a ν : ℝ) (y : Euc d) :
    |s83_L0 a ν h y| ≤ (|ν| * d * B2 + |a| * B1) * (1 + ‖y‖) := by
  have hB10 : 0 ≤ B1 := (norm_nonneg (fderiv ℝ h 0)).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ h) 0)).trans (hB2 0)
  unfold s83_L0
  have h1 := s83_lap_bound hB2 y
  have h2 : |fderiv ℝ h y y| ≤ B1 * ‖y‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ h y).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hB1 y) (norm_nonneg _))
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h3 : |ν| * |s83_lap h y| ≤ |ν| * (d * B2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h4 : |a| * |fderiv ℝ h y y| ≤ |a| * (B1 * ‖y‖) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  nlinarith [abs_nonneg ν, abs_nonneg a, norm_nonneg y, mul_nonneg (abs_nonneg ν) (Nat.cast_nonneg d : (0:ℝ) ≤ d),
    mul_nonneg (mul_nonneg (abs_nonneg ν) (Nat.cast_nonneg d : (0:ℝ) ≤ d)) hB20, mul_nonneg (abs_nonneg a) hB10,
    mul_nonneg (mul_nonneg (abs_nonneg a) hB10) (norm_nonneg y)]

theorem s83_L0_contOn {w : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)} (a ν : ℝ)
    (hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (w q.1) q.2) S)
    (hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (w q.1)) q.2) S) :
    ContinuousOn (fun q : ℝ × Euc d => s83_L0 a ν (w q.1) q.2) S := by
  unfold s83_L0 s83_lap
  refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const ?_)
    (ContinuousOn.mul continuousOn_const (hD1.clm_apply continuousOn_snd))
  refine continuousOn_finset_sum _ fun i _ => ?_
  exact (hD2.clm_apply continuousOn_const).clm_apply continuousOn_const

/-- **Mild (Duhamel) form of a classical backward solution.** -/
theorem s83_mild_form {w G : ℝ → Euc d → ℝ} {a ν t : ℝ} (ha : 0 < a) (hν : 0 < ν)
    (hc2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (w r)) {B : ℝ}
    (hB0 : ∀ r ∈ Set.Icc 0 t, ∀ y, |w r y| ≤ B)
    (hB1 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (w r) y‖ ≤ B)
    (hB2 : ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (w r)) y‖ ≤ B)
    (hwc : ContinuousOn (fun q : ℝ × Euc d => w q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hD1 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (w q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hD2 : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (w q.1)) q.2)
      (Set.Icc 0 t ×ˢ Set.univ))
    (hGc : ContinuousOn (fun q : ℝ × Euc d => G q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hder : ∀ x, ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun r' => w r' x) (-(G r x)) r) {BG : ℝ}
    (hGb : ∀ r ∈ Set.Icc 0 t, ∀ y, |G r y| ≤ BG * (1 + ‖y‖)) {r : ℝ} (hr : r ∈ Set.Icc 0 t)
    (x : Euc d) :
    w r x = s83_P a ν (t - r) (w t) x +
      ∫ s in r..t, s83_P a ν (s - r) (fun y => G s y - s83_L0 a ν (w s) y) x := by
  have hr0 : 0 ≤ r := hr.1
  have hB : 0 ≤ B := by
    have := (abs_nonneg (w r 0)).trans (hB0 r hr 0)
    exact this
  by_cases hrt : r = t
  · subst hrt
    rw [intervalIntegral.integral_same, sub_self, s83_P_zero, add_zero]
  have hrt' : r < t := lt_of_le_of_ne hr.2 hrt
  have hsub : ∀ s ∈ Set.Icc r t, s ∈ Set.Icc 0 t := fun s hs => ⟨hr0.trans hs.1, hs.2⟩
  -- the remainder `q = G - L_0 w`
  set q : ℝ → Euc d → ℝ := fun s y => G s y - s83_L0 a ν (w s) y with hq
  have hL0c := s83_L0_contOn a ν hD1 hD2
  have hqc : ContinuousOn (fun p : ℝ × Euc d => q p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
    hGc.sub hL0c
  have hqb : ∀ s ∈ Set.Icc 0 t, ∀ y, |q s y| ≤ (BG + (|ν| * d * B + |a| * B)) * (1 + ‖y‖) ^ 1 := by
    intro s hs y
    have h1 := hGb s hs y
    have h2 := s83_L0_bound (hB1 s hs) (hB2 s hs) a ν y
    simp only [hq, pow_one]
    refine (abs_sub _ _).trans ?_
    nlinarith
  -- `Θ s = (P_{s-r} w_s)(x)`
  set Θ : ℝ → ℝ := fun s => s83_P a ν (s - r) (w s) x with hΘ
  have hΘc : ContinuousOn Θ (Set.Icc r t) :=
    s83_cont_param (K := B) (p := 0) hr0 hr.2 hwc (fun s hs y => by simpa using hB0 s hs y) ha hν.le x
  have hΘd : ∀ s0 ∈ Set.Ioo r t, HasDerivAt Θ (-(s83_P a ν (s0 - r) (q s0) x)) s0 := by
    intro s0 hs0
    have hs0' : s0 ∈ Set.Ioo 0 t := ⟨by linarith [hs0.1], hs0.2⟩
    have hs0I : s0 ∈ Set.Icc 0 t := ⟨hs0'.1.le, hs0'.2.le⟩
    -- the `τ`-derivative
    have hΘ₁ : HasDerivAt (fun s => s83_P a ν (s - r) (w s0) x)
        (s83_P a ν (s0 - r) (s83_L0 a ν (w s0)) x) s0 := by
      have := s83_P_hasDerivAt (hc2 s0 hs0I) (hB0 s0 hs0I) (hB1 s0 hs0I) (hB2 s0 hs0I) ha hν
        (τ := s0 - r) (by linarith [hs0.1]) x
      exact this.comp_sub_const s0 r
    -- the datum derivative
    have hvc : ContinuousOn (fun q : ℝ × Euc d => (fun s y => -G s y) q.1 q.2)
        (Set.Icc 0 t ×ˢ Set.univ) := hGc.neg
    have hΘ₂ := s83_hasDerivAt_theta (w := w) (v := fun s y => -G s y) (r := r) (t := t) (s0 := s0)
      hr0 hs0.1 hs0.2 hwc hvc hder (Bv := BG)
      (fun s hs y => by simpa using hGb s hs y) ha hν.le x
    have hΘ := hΘ₁.add hΘ₂
    have hev : Θ =ᶠ[𝓝 s0] fun s => s83_P a ν (s - r) (w s0) x +
        ∫ z, (w s (s83_Y a ν r x z s) - w s0 (s83_Y a ν r x z s)) ∂(stdGaussian (Euc d)) := by
      filter_upwards [Ioo_mem_nhds hs0.1 hs0.2] with s hs
      have hsI : s ∈ Set.Icc 0 t := hsub s ⟨hs.1.le, hs.2.le⟩
      have i1 := s83_int_Y (f := w s) (hc2 s hsI).continuous (K := B) (p := 0)
        (fun y => by simpa using hB0 s hsI y) ha hν.le hs.1.le x
      have i2 := s83_int_Y (f := w s0) (hc2 s0 hs0I).continuous (K := B) (p := 0)
        (fun y => by simpa using hB0 s0 hs0I y) ha hν.le hs.1.le x
      rw [integral_sub i1 i2]
      have e : Θ s = ∫ z, w s (s83_Y a ν r x z s) ∂(stdGaussian (Euc d)) := rfl
      rw [e]
      simp only [s83_P_eq_Y]
      ring
    refine (hΘ.congr_of_eventuallyEq hev).congr_deriv ?_
    -- identify the derivative
    have iG := s83_int_Y (f := G s0) (by
        have : Continuous fun y : Euc d => (s0, y) := continuous_const.prodMk continuous_id
        exact hGc.comp_continuous this (fun y => ⟨hs0I, Set.mem_univ _⟩))
      (K := BG) (p := 1) (fun y => by simpa using hGb s0 hs0I y) ha hν.le hs0.1.le x
    have iL := s83_int_Y (f := s83_L0 a ν (w s0)) (by
        have : Continuous fun y : Euc d => (s0, y) := continuous_const.prodMk continuous_id
        exact hL0c.comp_continuous this (fun y => ⟨hs0I, Set.mem_univ _⟩))
      (K := |ν| * d * B + |a| * B) (p := 1)
      (fun y => by simpa using s83_L0_bound (hB1 s0 hs0I) (hB2 s0 hs0I) a ν y) ha hν.le hs0.1.le x
    simp only [hq, s83_P_eq_Y, integral_neg]
    rw [integral_sub iG iL]
    ring
  have hf'c : ContinuousOn (fun s => -(s83_P a ν (s - r) (q s) x)) (Set.Icc r t) :=
    (s83_cont_param (K := BG + (|ν| * d * B + |a| * B)) (p := 1) hr0 hr.2 hqc hqb ha hν.le x).neg
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hr.2 hΘc
    (fun s hs => (hΘd s hs).hasDerivWithinAt) (hf'c.intervalIntegrable_of_Icc hr.2)
  rw [intervalIntegral.integral_neg] at key
  have hΘr : Θ r = w r x := by
    simp only [hΘ, sub_self, s83_P_zero]
  have hΘt : Θ t = s83_P a ν (t - r) (w t) x := rfl
  rw [hΘr, hΘt] at key
  linarith

end HRS.MS.Wad
