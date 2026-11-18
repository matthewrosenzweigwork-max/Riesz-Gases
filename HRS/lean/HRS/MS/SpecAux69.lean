import HRS.MS.SpecAux68

/-!
# S8L: the Gross-Herbst differential inequality (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_diff_ineq`: for a positive subsolution `s` (`S8pSubsol`) of a measure
`μ` with log-Sobolev constant `C`, the truncated moments `Φ(q) = ∫ s m_ε(s)^{q-1} dμ` satisfy
`q Φ'(q) ≤ Φ(q) (log Φ(q) + K)` for `1 ≤ q ≤ 2`, `K = (2C/3)(a + b (3 H4/2 + 9/4))`.
-/

noncomputable section

open MeasureTheory Set Real

namespace HRS.MS.Spec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {s h : E → ℝ} {s0 a b H4 C : ℝ}

theorem s8p_u_contDiff (q : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {s : E → ℝ} (hs : ContDiff ℝ 2 s)
    (hpos : ∀ x, 0 < s x) : ContDiff ℝ 2 (fun x => s8p_Uq q ε (s x)) :=
  contDiff_iff_contDiffAt.2 fun x => (s8p_U_contDiffAt q hε (hpos x)).comp x hs.contDiffAt

theorem s8p_u_fderiv (q : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {s : E → ℝ} (hs : ContDiff ℝ 2 s)
    (hpos : ∀ x, 0 < s x) (x : E) :
    ‖fderiv ℝ (fun x => s8p_Uq q ε (s x)) x‖ ^ 2 = s8p_Ud q ε (s x) ^ 2 * ‖fderiv ℝ s x‖ ^ 2 := by
  have h1 := (s8p_U_hasDerivAt q hε (hpos x)).comp_hasFDerivAt x
    ((hs.differentiable (by norm_num)) x).hasFDerivAt
  have h2 : fderiv ℝ (fun x => s8p_Uq q ε (s x)) x = s8p_Ud q ε (s x) • fderiv ℝ s x := h1.fderiv
  rw [h2, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Lower bound `Φ(q) ≥ 1/6`. -/
theorem s8p_Phi_ge (hyp : S8pSubsol μ s h s0 a b H4) [IsProbabilityMeasure μ]
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    1 / 6 ≤ ∫ x, s8p_U2 q ε (s x) ∂μ := by
  have hsm : Measurable s := hyp.cont.continuous.measurable
  have hpos : ∀ x, 0 < s x := fun x => lt_of_lt_of_le hyp.s0_pos (hyp.ge x)
  have hint := s8p_U2_integrable q hε hyp.s0_pos hsm hyp.int hyp.ge
  have h1 : Integrable (fun x => (s x - 1 / 2) / 3) μ :=
    ((hyp.int.sub (integrable_const (1 / 2 : ℝ))).div_const 3)
  have h2 := integral_mono h1 hint (fun x => s8p_U2_ge hq1 hq2 hε.le hε1 (hpos x))
  have h3 : ∫ x, (s x - 1 / 2) / 3 ∂μ = 1 / 6 := by
    rw [integral_div, integral_sub hyp.int (integrable_const _), hyp.one]
    simp; norm_num
  linarith


theorem s8p_T_le {t hh G U2 a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) (hh0 : 0 ≤ hh)
    (hG : 0 < G) (hU : U2 = t * G) (hG2 : G ^ 2 ≤ 1 + U2) :
    (a * t + b * hh * Real.sqrt t) * G ≤ (a + 3 * b / 4) * U2 + (b / 4) * (hh ^ 4 + 1) := by
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : hh * Real.sqrt t ≤ (hh ^ 2 + t) / 2 := by nlinarith [sq_nonneg (hh - Real.sqrt t)]
  have h2 : hh ^ 2 * G ≤ (hh ^ 4 + G ^ 2) / 2 := by nlinarith [sq_nonneg (hh ^ 2 - G)]
  have h3 : b * (hh * Real.sqrt t) * G ≤ b * ((hh ^ 2 + t) / 2) * G := by
    apply mul_le_mul_of_nonneg_right _ hG.le
    exact mul_le_mul_of_nonneg_left h1 hb
  have e : (a * t + b * hh * Real.sqrt t) * G = a * U2 + b * (hh * Real.sqrt t) * G := by
    rw [hU]; ring
  rw [e]
  have h4 : b * ((hh ^ 2 + t) / 2) * G = (b / 2) * (hh ^ 2 * G) + (b / 2) * U2 := by
    rw [hU]; ring
  have h5 : (b / 2) * (hh ^ 2 * G) ≤ (b / 2) * ((hh ^ 4 + 1 + U2) / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  nlinarith

/-- **Gross-Herbst differential inequality** for the truncated moments of a subsolution. -/
theorem s8p_diff_ineq [IsProbabilityMeasure μ] (hyp : S8pSubsol μ s h s0 a b H4)
    (hLSI : s8p_LSI μ C) (hC : 0 ≤ C) {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hq1 : 1 ≤ q)
    (hq2 : q ≤ 2) :
    q * ∫ x, s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x)) ∂μ ≤
      (∫ x, s8p_U2 q ε (s x) ∂μ) * (Real.log (∫ x, s8p_U2 q ε (s x) ∂μ) +
        (2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4))) := by
  have hs0 := hyp.s0_pos
  have hsm : Measurable s := hyp.cont.continuous.measurable
  have hpos : ∀ x, 0 < s x := fun x => lt_of_lt_of_le hs0 (hyp.ge x)
  have hU2int := s8p_U2_integrable q hε hs0 hsm hyp.int hyp.ge
  have hΦ := s8p_Phi_ge hyp hε hε1 hq1 hq2
  have hdΦint := s8p_dPhi_integrable hε hs0 hsm hyp.int hyp.ge q
  set Φ := ∫ x, s8p_U2 q ε (s x) ∂μ with hΦdef
  set u : E → ℝ := fun x => s8p_Uq q ε (s x) with hu
  have hucd : ContDiff ℝ 2 u := s8p_u_contDiff q hε.le hyp.cont hpos
  have hu2 : ∀ x, u x ^ 2 = s8p_U2 q ε (s x) := fun x => s8p_U_sq hε.le (hpos x)
  have hum : Measurable u := hucd.continuous.measurable
  have hmem : MemLp u 2 μ := (memLp_two_iff_integrable_sq hum.aestronglyMeasurable).2
    (by simpa [hu2] using hU2int)
  obtain ⟨hI2, hA2int', hE'⟩ := hyp.en (s8p_G q ε) (s8p_G_contDiffOn q hε.le) (s8p_G_bounds q hε hs0)
    (fun t ht => (s8p_G_pos hε.le ht).le) (fun t ht => s8p_Gd_nonneg hq1 hε.le ht)
  set D : E → ℝ := fun x => ‖fderiv ℝ s x‖ ^ 2 with hD
  have hDm : Measurable D := ((hyp.cont.continuous_fderiv (by norm_num)).norm.pow 2).measurable
  have hD0 : ∀ x, 0 ≤ D x := fun x => sq_nonneg _
  have hdG : ∀ x, deriv (s8p_G q ε) (s x) = s8p_Gd q ε (s x) := fun x =>
    (s8p_G_hasDerivAt q hε.le (hpos x)).deriv
  simp only [hdG] at hI2 hE'
  have hGm : Measurable fun x => s8p_G q ε (s x) := by
    unfold s8p_G s8p_hm; fun_prop
  -- the source term and its majorant
  set T : E → ℝ := fun x => (a * s x + b * h x * Real.sqrt (s x)) * s8p_G q ε (s x) with hTdef
  set Tub : E → ℝ := fun x => (a + 3 * b / 4) * s8p_U2 q ε (s x) + (b / 4) * (h x ^ 4 + 1) with hTub
  have h41 : Integrable (fun x => h x ^ 4 + 1) μ := hyp.h4_int.add (integrable_const (1 : ℝ))
  have hTub_int : Integrable Tub μ :=
    (hU2int.const_mul _).add (h41.const_mul _)
  have hG_pos : ∀ x, 0 < s8p_G q ε (s x) := fun x => s8p_G_pos hε.le (hpos x)
  have hTle : ∀ x, T x ≤ Tub x := fun x =>
    s8p_T_le hyp.a_nonneg hyp.b_nonneg (hpos x) (hyp.h_nonneg x) (hG_pos x) rfl
      (s8p_G_sq_le hq1 hq2 hε.le (hpos x))
  have hT0 : ∀ x, 0 ≤ T x := fun x => by
    have := hyp.h_nonneg x
    have := hG_pos x
    have := hpos x
    have := hyp.a_nonneg; have := hyp.b_nonneg
    simp only [hTdef]; positivity
  have hTm : Measurable T := by
    simp only [hTdef]
    have := hyp.h_meas
    unfold s8p_G s8p_hm
    fun_prop
  have hTint : Integrable T μ := Integrable.mono' hTub_int hTm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hT0 x)]; exact hTle x)
  -- the good term
  set A2 : E → ℝ := fun x => s8p_G q ε (s x) * D x / (2 * s x) with hA2
  have hA2m : Measurable A2 := by
    simp only [hA2]
    have := hDm
    unfold s8p_G s8p_hm
    fun_prop
  have hA20 : ∀ x, 0 ≤ A2 x := fun x => by
    have := hG_pos x; have := hD0 x; have := hpos x
    simp only [hA2]; positivity
  have hA2int : Integrable A2 μ := hA2int'
  -- gradient of u
  have hgrad : ∀ x, ‖fderiv ℝ u x‖ ^ 2 ≤ (2 / 3) * (s8p_Gd q ε (s x) * D x + A2 x) := fun x => by
    rw [hu, s8p_u_fderiv q hε.le hyp.cont hpos x]
    have h1 := s8p_Ud_sq_le hq1 hq2 hε.le (hpos x)
    have h2 := mul_le_mul_of_nonneg_right h1 (hD0 x)
    have e : (2 / 3 * (s8p_Gd q ε (s x) + s8p_G q ε (s x) / (2 * s x))) * D x =
        2 / 3 * (s8p_Gd q ε (s x) * D x + A2 x) := by
      simp only [hA2]; ring
    simp only [hD] at h2 ⊢
    nlinarith
  have hgrad_meas : Measurable fun x => ‖fderiv ℝ u x‖ ^ 2 :=
    ((hucd.continuous_fderiv (by norm_num)).norm.pow 2).measurable
  have hgrad_int : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2) μ := by
    refine Integrable.mono' (((hI2.add hA2int).const_mul (2 / 3 : ℝ))) hgrad_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgrad x
  obtain ⟨hlogint, hlsi⟩ := hLSI u hucd hmem hgrad_int
  simp only [hu2] at hlogint hlsi
  -- entropy lower bound
  have hent : q * ∫ x, s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x)) ∂μ ≤
      ∫ x, s8p_U2 q ε (s x) * Real.log (s8p_U2 q ε (s x)) ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono (hdΦint.const_mul q) hlogint (fun x => s8p_U2_log_ge hq1 hε.le (hpos x))
  -- energy
  have hE : ∫ x, s8p_Gd q ε (s x) * D x ∂μ + ∫ x, A2 x ∂μ ≤ ∫ x, T x ∂μ := hE'
  have hgrad_int2 : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ ≤ (2 / 3) * ∫ x, T x ∂μ := by
    have h1 : ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ ≤ ∫ x, (2 / 3) * (s8p_Gd q ε (s x) * D x + A2 x) ∂μ :=
      integral_mono hgrad_int ((hI2.add hA2int).const_mul _) hgrad
    rw [integral_const_mul, integral_add hI2 hA2int] at h1
    linarith
  have hTint2 : ∫ x, T x ∂μ ≤ (a + 3 * b / 4) * Φ + (b / 4) * (H4 + 1) := by
    have h1 : ∫ x, T x ∂μ ≤ ∫ x, Tub x ∂μ := integral_mono hTint hTub_int hTle
    have h2 : ∫ x, Tub x ∂μ = (a + 3 * b / 4) * Φ + (b / 4) * (∫ x, h x ^ 4 ∂μ + 1) := by
      simp only [hTub]
      rw [integral_add (hU2int.const_mul _) (h41.const_mul _),
        integral_const_mul, integral_const_mul, integral_add hyp.h4_int (integrable_const _)]
      simp [hΦdef]
    have h3 := hyp.h4_le
    have hb := hyp.b_nonneg
    nlinarith
  have hH4 : 0 ≤ H4 := le_trans (integral_nonneg fun x => by positivity) hyp.h4_le
  have hK : (b / 4) * (H4 + 1) ≤ (3 * b / 2 * (H4 + 1)) * Φ := by
    have hb := hyp.b_nonneg
    have : 0 ≤ b * (H4 + 1) := by positivity
    nlinarith
  have hCg : C * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ ≤ C * ((2 / 3) * ∫ x, T x ∂μ) :=
    mul_le_mul_of_nonneg_left hgrad_int2 hC
  have ha := hyp.a_nonneg
  have hb := hyp.b_nonneg
  have hfin : C * ((2 / 3) * ∫ x, T x ∂μ) ≤ (2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4)) * Φ := by
    have h1 : ∫ x, T x ∂μ ≤ (a + b * (3 * H4 / 2 + 9 / 4)) * Φ := by nlinarith
    have : (2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4)) * Φ =
        C * ((2 / 3) * ((a + b * (3 * H4 / 2 + 9 / 4)) * Φ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) hC
  nlinarith

end HRS.MS.Spec
