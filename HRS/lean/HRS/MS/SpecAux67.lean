import Mathlib

/-!
# S8L: calculus of the Herbst truncation (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `ε ≥ 0` put `m_ε(t) = t/(1+εt)`, `G_q(t) = m_ε(t)^{q-1}`,
`u_q(t)² = t m_ε(t)^{q-1}`.  Pointwise facts used by the Gross-Herbst argument on a nonnegative subsolution `s`:
the derivative formulas, the key inequality `(u_q')² ≤ (2/3)(G_q' + G_q/(2t))` for `1 ≤ q ≤ 2`, and the
differentiation under the integral sign of `Φ(q) = ∫ s m_ε(s)^{q-1}`.
-/

noncomputable section

open Real MeasureTheory

namespace HRS.MS.Spec

/-- Truncation `m_ε(t) = t / (1 + ε t)`. -/
def s8p_hm (ε t : ℝ) : ℝ := t / (1 + ε * t)

theorem s8p_hm_pos {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : 0 < s8p_hm ε t := by
  unfold s8p_hm; positivity

theorem s8p_hm_le {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : s8p_hm ε t ≤ t := by
  unfold s8p_hm
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hε (sq_nonneg t)]

theorem s8p_hm_lt {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) : s8p_hm ε t < 1 / ε := by
  unfold s8p_hm
  rw [div_lt_div_iff₀ (by positivity) hε]
  nlinarith

theorem s8p_hm_mono {ε : ℝ} (hε : 0 ≤ ε) {t0 t : ℝ} (ht0 : 0 < t0) (h : t0 ≤ t) :
    s8p_hm ε t0 ≤ s8p_hm ε t := by
  unfold s8p_hm
  have ht : 0 < t := lt_of_lt_of_le ht0 h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hε (sub_nonneg.2 h), ht0]

theorem s8p_hm_hasDerivAt {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    HasDerivAt (s8p_hm ε) (1 / (1 + ε * t) ^ 2) t := by
  have h1 : (1 + ε * t) ≠ 0 := by positivity
  have h2 : HasDerivAt (fun x : ℝ => 1 + ε * x) ε t := by
    simpa using ((hasDerivAt_id t).const_mul ε).const_add 1
  have := (hasDerivAt_id t).div h2 h1
  have e : s8p_hm ε = fun x => id x / (1 + ε * x) := by funext x; rfl
  rw [e]
  convert this using 1
  simp only [id]; field_simp; ring


/-- `G_q(t) = m_ε(t)^{q-1}`. -/
def s8p_G (q ε t : ℝ) : ℝ := (s8p_hm ε t) ^ (q - 1)

/-- `u_q(t)^2 = t m_ε(t)^{q-1}`. -/
def s8p_U2 (q ε t : ℝ) : ℝ := t * s8p_G q ε t

/-- `u_q(t) = sqrt (t m_ε(t)^{q-1})`. -/
def s8p_Uq (q ε t : ℝ) : ℝ := Real.sqrt (s8p_U2 q ε t)

/-- `G_q'`. -/
def s8p_Gd (q ε t : ℝ) : ℝ := (q - 1) * s8p_G q ε t / (t * (1 + ε * t))

/-- `(u_q^2)'`. -/
def s8p_U2d (q ε t : ℝ) : ℝ := s8p_G q ε t * (1 + (q - 1) / (1 + ε * t))

/-- `u_q'`. -/
def s8p_Ud (q ε t : ℝ) : ℝ := s8p_U2d q ε t / (2 * s8p_Uq q ε t)

theorem s8p_G_pos {q ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : 0 < s8p_G q ε t :=
  Real.rpow_pos_of_pos (s8p_hm_pos hε ht) _

theorem s8p_G_hasDerivAt (q : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    HasDerivAt (s8p_G q ε) (s8p_Gd q ε t) t := by
  have hm := s8p_hm_pos hε ht
  have h := (s8p_hm_hasDerivAt hε ht).rpow_const (p := q - 1) (Or.inl hm.ne')
  have e1 : s8p_hm ε t ^ (q - 1 - 1) = s8p_hm ε t ^ (q - 1) / s8p_hm ε t :=
    Real.rpow_sub_one hm.ne' _
  have e : s8p_G q ε = fun y => s8p_hm ε y ^ (q - 1) := by funext y; rfl
  rw [e]
  convert h using 1
  unfold s8p_Gd s8p_G
  rw [e1]
  unfold s8p_hm
  have h1 : (1 + ε * t) ≠ 0 := by positivity
  field_simp

theorem s8p_U2_hasDerivAt (q : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    HasDerivAt (s8p_U2 q ε) (s8p_U2d q ε t) t := by
  have h := (hasDerivAt_id t).mul (s8p_G_hasDerivAt q hε ht)
  have e : s8p_U2 q ε = fun y => id y * s8p_G q ε y := by funext y; rfl
  rw [e]
  convert h using 1
  unfold s8p_U2d s8p_Gd
  simp only [id]
  have h1 : (1 + ε * t) ≠ 0 := by positivity
  field_simp

theorem s8p_U2_pos {q ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : 0 < s8p_U2 q ε t :=
  mul_pos ht (s8p_G_pos hε ht)

theorem s8p_U_pos {q ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : 0 < s8p_Uq q ε t :=
  Real.sqrt_pos.2 (s8p_U2_pos hε ht)

theorem s8p_U_sq {q ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) : s8p_Uq q ε t ^ 2 = s8p_U2 q ε t :=
  Real.sq_sqrt (s8p_U2_pos hε ht).le

theorem s8p_U_hasDerivAt (q : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    HasDerivAt (s8p_Uq q ε) (s8p_Ud q ε t) t := by
  have h := (s8p_U2_hasDerivAt q hε ht).sqrt (s8p_U2_pos hε ht).ne'
  exact h

/-- The key pointwise inequality `(u_q')² ≤ (2/3)(G_q' + G_q/(2t))` for `1 ≤ q ≤ 2`. -/
theorem s8p_Ud_sq_le {q ε t : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hε : 0 ≤ ε) (ht : 0 < t) :
    s8p_Ud q ε t ^ 2 ≤ (2 / 3) * (s8p_Gd q ε t + s8p_G q ε t / (2 * t)) := by
  have hG := s8p_G_pos (q := q) hε ht
  have hU := s8p_U_pos (q := q) hε ht
  have hUsq := s8p_U_sq (q := q) hε ht
  set G := s8p_G q ε t with hGdef
  set ρ : ℝ := 1 / (1 + ε * t) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_one (by positivity)]; nlinarith [mul_nonneg hε ht.le]
  set x : ℝ := (q - 1) * ρ with hx
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) hρ0.le
  have hx1 : x ≤ 1 := by
    calc x ≤ 1 * 1 := mul_le_mul (by linarith) hρ1 hρ0.le (by norm_num)
      _ = 1 := by norm_num
  have e1 : s8p_U2d q ε t = G * (1 + x) := by
    unfold s8p_U2d; rw [← hGdef, hx, hρ]; ring
  have e2 : s8p_Gd q ε t = G * x / t := by
    unfold s8p_Gd; rw [← hGdef, hx, hρ]; field_simp
  have e3 : s8p_U2 q ε t = t * G := rfl
  have e4 : s8p_Ud q ε t ^ 2 = G * (1 + x) ^ 2 / (4 * t) := by
    unfold s8p_Ud
    rw [div_pow, mul_pow, hUsq, e1, e3]
    field_simp
    norm_num
  rw [e4, e2]
  have key : (1 + x) ^ 2 / 4 ≤ (2 / 3) * (x + 1 / 2) := by nlinarith
  have : G * (1 + x) ^ 2 / (4 * t) = (G / t) * ((1 + x) ^ 2 / 4) := by field_simp
  rw [this]
  have e5 : (2 / 3) * (G * x / t + G / (2 * t)) = (G / t) * ((2 / 3) * (x + 1 / 2)) := by
    field_simp
  rw [e5]
  exact mul_le_mul_of_nonneg_left key (by positivity)


theorem s8p_U2_hasDerivAt_q (q0 : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    HasDerivAt (fun q => s8p_U2 q ε t) (s8p_U2 q0 ε t * Real.log (s8p_hm ε t)) q0 := by
  have hm := s8p_hm_pos hε ht
  have h1 : HasDerivAt (fun q : ℝ => s8p_hm ε t ^ (q - 1)) (s8p_hm ε t ^ (q0 - 1) * Real.log (s8p_hm ε t)) q0 := by
    have := (Real.hasStrictDerivAt_const_rpow hm (q0 - 1)).hasDerivAt
    have h2 : HasDerivAt (fun q : ℝ => q - 1) 1 q0 := by simpa using (hasDerivAt_id q0).sub_const 1
    have h3 := HasDerivAt.comp q0 this h2
    have h4 : (1 : ℝ) = 1 := rfl
    simpa [Function.comp_def, mul_one] using h3
  have := h1.const_mul t
  unfold s8p_U2 s8p_G
  convert this using 1
  ring

theorem s8p_rpow_le_pow_add_pow {m r R : ℝ} (hm : 0 < m) (hr : |r| ≤ R) :
    m ^ r ≤ m ^ R + m ^ (-R) := by
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  have h1 := abs_le.1 hr
  rcases le_total 1 m with h | h
  · have : m ^ r ≤ m ^ R := Real.rpow_le_rpow_of_exponent_le h h1.2
    have : 0 ≤ m ^ (-R) := (Real.rpow_pos_of_pos hm _).le
    linarith
  · have : m ^ r ≤ m ^ (-R) := Real.rpow_le_rpow_of_exponent_ge hm h h1.1
    have : 0 ≤ m ^ R := (Real.rpow_pos_of_pos hm _).le
    linarith


/-- Upper bound for `m_ε(t)^r` on `t ≥ s0`, `|r| ≤ R`. -/
def s8p_Bm (ε s0 R : ℝ) : ℝ := (1 / ε) ^ R + (s8p_hm ε s0) ^ (-R)

/-- Bound for `|log m_ε(t)|` on `t ≥ s0`. -/
def s8p_Lm (ε s0 : ℝ) : ℝ := |Real.log (s8p_hm ε s0)| + |Real.log ε|

theorem s8p_hm_rpow_le {ε s0 t r R : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) (ht : s0 ≤ t) (hr : |r| ≤ R) :
    s8p_hm ε t ^ r ≤ s8p_Bm ε s0 R := by
  have ht0 : 0 < t := lt_of_lt_of_le hs0 ht
  have hm := s8p_hm_pos hε.le ht0
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  refine (s8p_rpow_le_pow_add_pow hm hr).trans ?_
  unfold s8p_Bm
  have h1 : s8p_hm ε t ^ R ≤ (1 / ε) ^ R :=
    Real.rpow_le_rpow hm.le (s8p_hm_lt hε ht0).le hR
  have h2 : s8p_hm ε t ^ (-R) ≤ (s8p_hm ε s0) ^ (-R) :=
    Real.rpow_le_rpow_of_nonpos (s8p_hm_pos hε.le hs0) (s8p_hm_mono hε.le hs0 ht) (by linarith)
  linarith

theorem s8p_abs_log_hm_le {ε s0 t : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) (ht : s0 ≤ t) :
    |Real.log (s8p_hm ε t)| ≤ s8p_Lm ε s0 := by
  have ht0 : 0 < t := lt_of_lt_of_le hs0 ht
  have hm := s8p_hm_pos hε.le ht0
  have hm0 := s8p_hm_pos hε.le hs0
  have h1 : Real.log (s8p_hm ε s0) ≤ Real.log (s8p_hm ε t) :=
    Real.log_le_log hm0 (s8p_hm_mono hε.le hs0 ht)
  have h2 : Real.log (s8p_hm ε t) ≤ Real.log (1 / ε) :=
    Real.log_le_log hm (s8p_hm_lt hε ht0).le
  have h3 : Real.log (1 / ε) = - Real.log ε := by rw [one_div, Real.log_inv]
  unfold s8p_Lm
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (s8p_hm ε s0)); have := abs_nonneg (Real.log ε); linarith
  · have := neg_le_abs (Real.log ε); have := abs_nonneg (Real.log (s8p_hm ε s0)); linarith

theorem s8p_U2_le {q ε s0 t R : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) (ht : s0 ≤ t) (hq : |q - 1| ≤ R) :
    |s8p_U2 q ε t| ≤ t * s8p_Bm ε s0 R := by
  have ht0 : 0 < t := lt_of_lt_of_le hs0 ht
  have := s8p_U2_pos (q := q) hε.le ht0
  rw [abs_of_pos this]
  unfold s8p_U2 s8p_G
  exact mul_le_mul_of_nonneg_left (s8p_hm_rpow_le hε hs0 ht hq) ht0.le

theorem s8p_U2_log_le {q ε s0 t R : ℝ} (hε : 0 < ε) (hs0 : 0 < s0) (ht : s0 ≤ t) (hq : |q - 1| ≤ R) :
    |s8p_U2 q ε t * Real.log (s8p_hm ε t)| ≤ t * (s8p_Bm ε s0 R * s8p_Lm ε s0) := by
  rw [abs_mul]
  calc |s8p_U2 q ε t| * |Real.log (s8p_hm ε t)| ≤ (t * s8p_Bm ε s0 R) * s8p_Lm ε s0 :=
        mul_le_mul (s8p_U2_le hε hs0 ht hq) (s8p_abs_log_hm_le hε hs0 ht) (abs_nonneg _)
          (by have := s8p_U2_le hε hs0 ht hq; exact (abs_nonneg _).trans this)
    _ = t * (s8p_Bm ε s0 R * s8p_Lm ε s0) := by ring

section Phi

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {s : E → ℝ} {ε s0 : ℝ}

theorem s8p_U2_integrable (q : ℝ) (hε : 0 < ε) (hs0 : 0 < s0) (hs : Measurable s)
    (hint : Integrable s μ) (hge : ∀ x, s0 ≤ s x) :
    Integrable (fun x => s8p_U2 q ε (s x)) μ := by
  refine Integrable.mono' (hint.mul_const (s8p_Bm ε s0 |q - 1|)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have hm : Measurable fun x => s8p_U2 q ε (s x) := by
      unfold s8p_U2 s8p_G s8p_hm
      fun_prop
    exact hm.aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using s8p_U2_le (q := q) hε hs0 (hge x) le_rfl

theorem s8p_Phi_hasDerivAt (hε : 0 < ε) (hs0 : 0 < s0) (hs : Measurable s)
    (hint : Integrable s μ) (hge : ∀ x, s0 ≤ s x) (q0 : ℝ) :
    HasDerivAt (fun q => ∫ x, s8p_U2 q ε (s x) ∂μ)
      (∫ x, s8p_U2 q0 ε (s x) * Real.log (s8p_hm ε (s x)) ∂μ) q0 := by
  have hmeas : ∀ q : ℝ, Measurable fun x => s8p_U2 q ε (s x) := fun q => by
    unfold s8p_U2 s8p_G s8p_hm
    fun_prop
  have hmeas' : Measurable fun x => s8p_U2 q0 ε (s x) * Real.log (s8p_hm ε (s x)) := by
    have := hmeas q0
    unfold s8p_hm
    unfold s8p_U2 s8p_G s8p_hm at this
    fun_prop
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun q x => s8p_U2 q ε (s x))
    (F' := fun q x => s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x))) (x₀ := q0)
    (bound := fun x => s x * (s8p_Bm ε s0 (|q0 - 1| + 1) * s8p_Lm ε s0))
    (s := Metric.ball q0 1) (Metric.ball_mem_nhds q0 one_pos)
    (Filter.Eventually.of_forall fun q => (hmeas q).aestronglyMeasurable)
    (s8p_U2_integrable q0 hε hs0 hs hint hge) hmeas'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x q hq => ?_)
    (hint.mul_const _)
    (Filter.Eventually.of_forall fun x q _ => s8p_U2_hasDerivAt_q q hε.le (lt_of_lt_of_le hs0 (hge x)))
  · exact this.2
  · have hq' : |q - 1| ≤ |q0 - 1| + 1 := by
      have : |q - q0| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hq
      calc |q - 1| = |(q0 - 1) + (q - q0)| := by ring_nf
        _ ≤ |q0 - 1| + |q - q0| := abs_add_le _ _
        _ ≤ |q0 - 1| + 1 := by linarith
    simpa [Real.norm_eq_abs] using s8p_U2_log_le hε hs0 (hge x) hq'

end Phi


theorem s8p_U_contDiffAt (q : ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) :
    ContDiffAt ℝ 2 (s8p_Uq q ε) t := by
  have h1 : ContDiffAt ℝ 2 (fun x : ℝ => 1 + ε * x) t := by fun_prop
  have h1' : (1 + ε * t) ≠ 0 := by positivity
  have h2 : ContDiffAt ℝ 2 (fun x : ℝ => x / (1 + ε * x)) t := contDiffAt_id.div h1 h1'
  have hm : (t / (1 + ε * t)) ≠ 0 := by positivity
  have h3 : ContDiffAt ℝ 2 (fun x : ℝ => (x / (1 + ε * x)) ^ (q - 1)) t :=
    h2.rpow_const_of_ne hm
  have h4 : ContDiffAt ℝ 2 (fun x : ℝ => x * (x / (1 + ε * x)) ^ (q - 1)) t := contDiffAt_id.mul h3
  have hne : t * (t / (1 + ε * t)) ^ (q - 1) ≠ 0 := by positivity
  exact h4.sqrt hne

end HRS.MS.Spec
