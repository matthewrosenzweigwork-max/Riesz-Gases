import HRS.Whole.Basic

/-!
# Q33b helpers (supplement S11.5, whole-space clause): the logarithmic row bound with explicit constants

Packet Q33b.  For the logarithmic kernel `g = rieszKernel d 0 = -log|·|` put `⟨x⟩ = √(1+|x|²)`, `ℓ = log⟨x⟩ ≥ 0` and
`b(x,y) = ℓ x + ℓ y + g(x-y) = log(⟨x⟩⟨y⟩/|x-y|) ≥ 0`.  The row bound `sup_y ∫ exp(ε b(x,y)) μ(dx) ≤ C` is proved with
constants depending only on `d, ε, C₁, a₀` (never on the density), where `ρ ≤ C₁ exp(-a₀|x|²)`.
-/

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace HRS.Whole

/-- `⟨x⟩ = √(1+|x|²)`. -/
def q33b_ang {d : ℕ} (x : Euc d) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

/-- `ℓ(x) = log⟨x⟩`. -/
def q33b_ell {d : ℕ} (x : Euc d) : ℝ := Real.log (q33b_ang x)

/-- `b(x,y) = ℓ(x) + ℓ(y) + g(x-y)` for the logarithmic kernel `g = rieszKernel d 0`. -/
def q33b_b {d : ℕ} (x y : Euc d) : ℝ := q33b_ell x + q33b_ell y + rieszKernel d 0 (x - y)

/-- The dominating function `C₁ (1+|x|²) exp(-a₀|x|²)`. -/
def q33b_Phi {d : ℕ} (C₁ a₀ : ℝ) (x : Euc d) : ℝ := C₁ * ((1 + ‖x‖ ^ 2) * Real.exp (-a₀ * ‖x‖ ^ 2))

/-- The local integral `∫_{|z|<1} |z|^{-ε} dz` (as a lower integral). -/
def q33b_loc (d : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Euc d, ENNReal.ofReal (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) z)

/-- The uniform row constant `K = C₁(1+1/a₀)·∫_{|z|<1}|z|^{-ε} + 2∫Φ`. -/
def q33b_K (d : ℕ) (ε C₁ a₀ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (C₁ * (1 + 1 / a₀)) * q33b_loc d ε +
    ENNReal.ofReal 2 * ∫⁻ x : Euc d, ENNReal.ofReal (q33b_Phi C₁ a₀ x)

theorem q33b_rk {d : ℕ} (z : Euc d) : rieszKernel d 0 z = -Real.log ‖z‖ := by
  simp [rieszKernel]

theorem q33b_ang_sq {d : ℕ} (x : Euc d) : q33b_ang x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold q33b_ang
  exact Real.sq_sqrt (by positivity)

theorem q33b_ang_ge_one {d : ℕ} (x : Euc d) : 1 ≤ q33b_ang x := by
  have h : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  unfold q33b_ang
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt h

theorem q33b_ang_pos {d : ℕ} (x : Euc d) : 0 < q33b_ang x :=
  lt_of_lt_of_le one_pos (q33b_ang_ge_one x)

theorem q33b_ell_nonneg {d : ℕ} (x : Euc d) : 0 ≤ q33b_ell x :=
  Real.log_nonneg (q33b_ang_ge_one x)

theorem q33b_norm_le_ang_mul {d : ℕ} (x y : Euc d) : ‖x - y‖ ≤ q33b_ang x * q33b_ang y := by
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have h2 : ‖x‖ + ‖y‖ ≤ q33b_ang x * q33b_ang y := by
    unfold q33b_ang
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2)]
    calc ‖x‖ + ‖y‖ = Real.sqrt ((‖x‖ + ‖y‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (‖x‖ * ‖y‖ - 1)])
  linarith

theorem q33b_b_nonneg {d : ℕ} (x y : Euc d) : 0 ≤ q33b_b x y := by
  unfold q33b_b
  rw [q33b_rk]
  have h1 := q33b_ell_nonneg x
  have h2 := q33b_ell_nonneg y
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with h | h
  · rw [← h, Real.log_zero]
    linarith
  · have hl : Real.log ‖x - y‖ ≤ q33b_ell x + q33b_ell y := by
      unfold q33b_ell
      rw [← Real.log_mul (ne_of_gt (q33b_ang_pos x)) (ne_of_gt (q33b_ang_pos y))]
      exact Real.log_le_log h (q33b_norm_le_ang_mul x y)
    linarith

theorem q33b_b_comm {d : ℕ} (x y : Euc d) : q33b_b x y = q33b_b y x := by
  unfold q33b_b
  rw [q33b_rk, q33b_rk, norm_sub_rev]
  ring

theorem q33b_b_self {d : ℕ} (x : Euc d) : q33b_b x x = 2 * q33b_ell x := by
  unfold q33b_b
  rw [sub_self, q33b_rk, norm_zero, Real.log_zero]
  ring

theorem q33b_ell_measurable {d : ℕ} : Measurable (fun x : Euc d => q33b_ell x) := by
  unfold q33b_ell q33b_ang
  exact ((measurable_const.add (measurable_norm.pow_const 2)).sqrt).log

theorem q33b_b_measurable {d : ℕ} : Measurable (fun p : Euc d × Euc d => q33b_b p.1 p.2) := by
  have hℓ : Measurable (fun x : Euc d => q33b_ell x) := q33b_ell_measurable
  have hkern : rieszKernel d 0 = fun z : Euc d => -Real.log ‖z‖ := funext q33b_rk
  have hg : Measurable (rieszKernel d 0) := by
    rw [hkern]
    exact (measurable_norm.log).neg
  unfold q33b_b
  exact ((hℓ.comp measurable_fst).add (hℓ.comp measurable_snd)).add
    (hg.comp (measurable_fst.sub measurable_snd))

theorem q33b_exp_b {d : ℕ} (ε : ℝ) (x y : Euc d) (hxy : x ≠ y) :
    Real.exp (ε * q33b_b x y) = q33b_ang x ^ ε * q33b_ang y ^ ε * ‖x - y‖ ^ (-ε) := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  rw [Real.rpow_def_of_pos (q33b_ang_pos x), Real.rpow_def_of_pos (q33b_ang_pos y),
    Real.rpow_def_of_pos hr, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold q33b_b q33b_ell
  rw [q33b_rk]
  ring

theorem q33b_lip {d : ℕ} (x y : Euc d) : q33b_ang y ≤ q33b_ang x + ‖x - y‖ := by
  have hx : ‖x‖ ≤ q33b_ang x := by
    have h := q33b_ang_sq x
    nlinarith [norm_nonneg x, q33b_ang_pos x]
  have hy1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have := norm_sub_le x (x - y)
    rwa [sub_sub_cancel] at this
  have hy2 : ‖y‖ ^ 2 ≤ (‖x‖ + ‖x - y‖) ^ 2 := by nlinarith [norm_nonneg y]
  have hsq : 1 + ‖y‖ ^ 2 ≤ (q33b_ang x + ‖x - y‖) ^ 2 := by
    have h := q33b_ang_sq x
    nlinarith [mul_le_mul_of_nonneg_right hx (norm_nonneg (x - y)), norm_nonneg (x - y)]
  show Real.sqrt (1 + ‖y‖ ^ 2) ≤ q33b_ang x + ‖x - y‖
  calc Real.sqrt (1 + ‖y‖ ^ 2) ≤ Real.sqrt ((q33b_ang x + ‖x - y‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = q33b_ang x + ‖x - y‖ := Real.sqrt_sq (add_nonneg (q33b_ang_pos x).le (norm_nonneg _))

/-- Pointwise row bound for `x ≠ y`. -/
theorem q33b_row_pt {d : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x y : Euc d) (hxy : x ≠ y) :
    Real.exp (ε * q33b_b x y) ≤ q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + q33b_ang x ^ ε := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hA := q33b_ang_pos x
  rw [q33b_exp_b ε x y hxy]
  have hBle : q33b_ang y ^ ε ≤ (q33b_ang x + ‖x - y‖) ^ ε :=
    Real.rpow_le_rpow (q33b_ang_pos y).le (q33b_lip x y) hε0.le
  have hsub : (q33b_ang x + ‖x - y‖) ^ ε ≤ q33b_ang x ^ ε + ‖x - y‖ ^ ε :=
    Real.rpow_add_le_add_rpow hA.le hr.le hε0.le hε1
  have hkey : ‖x - y‖ ^ ε * ‖x - y‖ ^ (-ε) = 1 := by
    rw [Real.rpow_neg hr.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr ε).ne']
  have hAA : q33b_ang x ^ ε * q33b_ang x ^ ε = q33b_ang x ^ (2 * ε) := by
    rw [← Real.rpow_add hA, show ε + ε = 2 * ε by ring]
  have hnn : 0 ≤ ‖x - y‖ ^ (-ε) := Real.rpow_nonneg hr.le _
  have hAnn : 0 ≤ q33b_ang x ^ ε := Real.rpow_nonneg hA.le _
  calc q33b_ang x ^ ε * q33b_ang y ^ ε * ‖x - y‖ ^ (-ε)
      ≤ q33b_ang x ^ ε * (q33b_ang x ^ ε + ‖x - y‖ ^ ε) * ‖x - y‖ ^ (-ε) := by
        apply mul_le_mul_of_nonneg_right _ hnn
        exact mul_le_mul_of_nonneg_left (hBle.trans hsub) hAnn
    _ = q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε)
          + q33b_ang x ^ ε * (‖x - y‖ ^ ε * ‖x - y‖ ^ (-ε)) := by
        rw [← hAA]; ring
    _ = q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + q33b_ang x ^ ε := by
        rw [hkey, mul_one]

theorem q33b_W_le {d : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : Euc d) :
    q33b_ang x ^ ε ≤ q33b_ang x ^ (2 * ε) ∧ q33b_ang x ^ (2 * ε) ≤ 1 + ‖x‖ ^ 2 := by
  have h1 := q33b_ang_ge_one x
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have h2 := Real.rpow_le_rpow_of_exponent_le h1 (show 2 * ε ≤ 2 by linarith)
    rw [Real.rpow_two, q33b_ang_sq] at h2
    exact h2

theorem q33b_Phi_nonneg {d : ℕ} {C₁ a₀ : ℝ} (hC : 0 ≤ C₁) (x : Euc d) : 0 ≤ q33b_Phi C₁ a₀ x :=
  mul_nonneg hC (mul_nonneg (by positivity) (Real.exp_pos _).le)

theorem q33b_Phi_le {d : ℕ} {C₁ a₀ : ℝ} (hC : 0 ≤ C₁) (ha : 0 < a₀) (x : Euc d) :
    q33b_Phi C₁ a₀ x ≤ C₁ * (1 + 1 / a₀) := by
  unfold q33b_Phi
  apply mul_le_mul_of_nonneg_left _ hC
  have ht0 : 0 ≤ ‖x‖ ^ 2 := by positivity
  generalize ‖x‖ ^ 2 = t at ht0 ⊢
  have h1 : a₀ * t + 1 ≤ Real.exp (a₀ * t) := by linarith [Real.add_one_le_exp (a₀ * t)]
  have h2 : Real.exp (-a₀ * t) * Real.exp (a₀ * t) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (-a₀ * t) * (1 + a₀ * t) ≤ 1 := by
    calc Real.exp (-a₀ * t) * (1 + a₀ * t) ≤ Real.exp (-a₀ * t) * Real.exp (a₀ * t) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := h2
  have hinv : a₀ * (1 / a₀) = 1 := by field_simp
  have h4 : (1 + 1 / a₀) * (1 + a₀ * t) = 1 + t + (a₀ * t + 1 / a₀) := by
    linear_combination t * hinv
  have h5 : 1 + t ≤ (1 + 1 / a₀) * (1 + a₀ * t) := by
    rw [h4]
    have : 0 ≤ a₀ * t + 1 / a₀ := by
      have : 0 ≤ 1 / a₀ := by positivity
      nlinarith
    linarith
  have hpos : 0 ≤ 1 + 1 / a₀ := by positivity
  calc (1 + t) * Real.exp (-a₀ * t) ≤ (1 + 1 / a₀) * (1 + a₀ * t) * Real.exp (-a₀ * t) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = (1 + 1 / a₀) * (Real.exp (-a₀ * t) * (1 + a₀ * t)) := by ring
    _ ≤ (1 + 1 / a₀) * 1 := mul_le_mul_of_nonneg_left h3 hpos
    _ = 1 + 1 / a₀ := mul_one _

theorem q33b_gauss {d : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (c : ℂ))
    (by simpa using hc) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Complex.norm_exp, ← Complex.ofReal_pow]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, sub_zero, neg_mul, add_zero, Complex.neg_im]

theorem q33b_Phi_le_gauss {a₀ : ℝ} (ha : 0 < a₀) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) * Real.exp (-a₀ * t) ≤ (1 + 2 / a₀) * Real.exp (-(a₀ / 2) * t) := by
  have h1 : a₀ / 2 * t + 1 ≤ Real.exp (a₀ / 2 * t) := by
    linarith [Real.add_one_le_exp (a₀ / 2 * t)]
  have hinv : a₀ * (2 / a₀) = 2 := by field_simp
  have h4 : (1 + 2 / a₀) * (1 + a₀ / 2 * t) = 1 + t + (a₀ / 2 * t + 2 / a₀) := by
    linear_combination (t / 2) * hinv
  have h5 : 1 + t ≤ (1 + 2 / a₀) * Real.exp (a₀ / 2 * t) := by
    have hpos : 0 ≤ 1 + 2 / a₀ := by positivity
    have : 0 ≤ a₀ / 2 * t + 2 / a₀ := by
      have : 0 ≤ 2 / a₀ := by positivity
      have : 0 ≤ a₀ / 2 * t := by positivity
      linarith
    calc 1 + t ≤ (1 + 2 / a₀) * (1 + a₀ / 2 * t) := by rw [h4]; linarith
      _ ≤ (1 + 2 / a₀) * Real.exp (a₀ / 2 * t) := mul_le_mul_of_nonneg_left (by linarith) hpos
  calc (1 + t) * Real.exp (-a₀ * t) ≤ (1 + 2 / a₀) * Real.exp (a₀ / 2 * t) * Real.exp (-a₀ * t) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = (1 + 2 / a₀) * Real.exp (-(a₀ / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem q33b_Phi_integrable {d : ℕ} {C₁ a₀ : ℝ} (hC : 0 ≤ C₁) (ha : 0 < a₀) :
    Integrable (fun x : Euc d => q33b_Phi C₁ a₀ x) := by
  have hG := (q33b_gauss (d := d) (c := a₀ / 2) (by positivity)).const_mul (C₁ * (1 + 2 / a₀))
  refine hG.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · unfold q33b_Phi
    exact (measurable_const.mul ((measurable_const.add (measurable_norm.pow_const 2)).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2))))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (q33b_Phi_nonneg hC x)]
    unfold q33b_Phi
    have := q33b_Phi_le_gauss ha (‖x‖ ^ 2) (by positivity)
    calc C₁ * ((1 + ‖x‖ ^ 2) * Real.exp (-a₀ * ‖x‖ ^ 2))
        ≤ C₁ * ((1 + 2 / a₀) * Real.exp (-(a₀ / 2) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left this hC
      _ = C₁ * (1 + 2 / a₀) * Real.exp (-(a₀ / 2) * ‖x‖ ^ 2) := by ring

theorem q33b_loc_lt_top {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hεd : ε < d) : q33b_loc d ε < ⊤ := by
  have hfin : Module.finrank ℝ (Euc d) = d := by simp
  have hint : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-ε)) (Metric.ball (0 : Euc d) 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : Euc d => ‖z‖ ^ (-ε))
      (C := 1) (α := ε) (r := 1) ?_ ?_ ?_ ?_
    · rw [hfin]; exact hd
    · rw [hfin]; exact hεd
    · refine Filter.Eventually.of_forall fun z => ?_
      simp only [one_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hI : Integrable (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)))
      (volume : Measure (Euc d)) :=
    (integrable_indicator_iff measurableSet_ball).2 hint
  exact hI.lintegral_lt_top

/-- Pointwise bound of the row integrand (all `x, y`). -/
theorem q33b_pt {d : ℕ} {ε C₁ a₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C₁) (ha : 0 < a₀)
    (x y : Euc d) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) :
    v * Real.exp (ε * q33b_b x y) ≤
      C₁ * (1 + 1 / a₀) * Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y)
        + 2 * q33b_Phi C₁ a₀ x := by
  have hA := q33b_ang_pos x
  have hWle := q33b_W_le (d := d) hε0 hε1 x
  have hWnn : 0 ≤ q33b_ang x ^ (2 * ε) := Real.rpow_nonneg hA.le _
  have hΦnn : 0 ≤ q33b_Phi C₁ a₀ x := q33b_Phi_nonneg hC x
  have hΦM : q33b_Phi C₁ a₀ x ≤ C₁ * (1 + 1 / a₀) := q33b_Phi_le hC ha x
  have hindnn : 0 ≤ Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y) :=
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) _
  -- `v W ≤ Φ` with `W = ⟨x⟩^{2ε}`
  have hPw : v * q33b_ang x ^ (2 * ε) ≤ q33b_Phi C₁ a₀ x := by
    unfold q33b_Phi
    have hE : 0 ≤ Real.exp (-a₀ * ‖x‖ ^ 2) := (Real.exp_pos _).le
    calc v * q33b_ang x ^ (2 * ε) ≤ (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) * q33b_ang x ^ (2 * ε) :=
          mul_le_mul_of_nonneg_right hv hWnn
      _ ≤ (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) * (1 + ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hWle.2 (mul_nonneg hC hE)
      _ = C₁ * ((1 + ‖x‖ ^ 2) * Real.exp (-a₀ * ‖x‖ ^ 2)) := by ring
  by_cases hxy : x = y
  · -- diagonal: `exp(ε b(x,x)) = ⟨x⟩^{2ε}`
    subst hxy
    have hexp : Real.exp (ε * q33b_b x x) = q33b_ang x ^ (2 * ε) := by
      rw [q33b_b_self, Real.rpow_def_of_pos hA]
      unfold q33b_ell
      congr 1
      ring
    rw [hexp]
    have : 0 ≤ C₁ * (1 + 1 / a₀) * Set.indicator (Metric.ball (0 : Euc d) 1)
        (fun z : Euc d => ‖z‖ ^ (-ε)) (x - x) := mul_nonneg (mul_nonneg hC (by positivity)) hindnn
    linarith
  · have hr : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have hmain : v * Real.exp (ε * q33b_b x y) ≤
        v * q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + v * q33b_ang x ^ (2 * ε) := by
      have h1 := q33b_row_pt hε0 hε1 x y hxy
      have hAε := hWle.1
      have hnn : 0 ≤ ‖x - y‖ ^ (-ε) := Real.rpow_nonneg hr.le _
      calc v * Real.exp (ε * q33b_b x y)
          ≤ v * (q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + q33b_ang x ^ ε) :=
            mul_le_mul_of_nonneg_left h1 hv0
        _ ≤ v * (q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + q33b_ang x ^ (2 * ε)) :=
            mul_le_mul_of_nonneg_left (by linarith) hv0
        _ = v * q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) + v * q33b_ang x ^ (2 * ε) := by ring
    rcases lt_or_ge ‖x - y‖ 1 with hs1 | hs1
    · have hind : Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y)
          = ‖x - y‖ ^ (-ε) := Set.indicator_of_mem (mem_ball_zero_iff.2 hs1) _
      rw [hind]
      have hM : v * q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) ≤ C₁ * (1 + 1 / a₀) * ‖x - y‖ ^ (-ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
        linarith
      linarith
    · have hind : Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y)
          = 0 := by
        refine Set.indicator_of_notMem (fun h => ?_) _
        have := mem_ball_zero_iff.1 h
        linarith
      rw [hind]
      have hle1 : ‖x - y‖ ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by linarith)
      have hvW : 0 ≤ v * q33b_ang x ^ (2 * ε) := mul_nonneg hv0 hWnn
      have hWle' : v * q33b_ang x ^ (2 * ε) * ‖x - y‖ ^ (-ε) ≤ v * q33b_ang x ^ (2 * ε) :=
        mul_le_of_le_one_right hvW hle1
      have : v * q33b_ang x ^ (2 * ε) ≤ q33b_Phi C₁ a₀ x := hPw
      nlinarith

/-- The row integral against `ρ dx`, uniformly in `y`. -/
theorem q33b_row {d : ℕ} {ε C₁ a₀ : ℝ} (hd : 1 ≤ d) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε < d)
    (hC : 0 ≤ C₁) (ha : 0 < a₀) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) (y : Euc d) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂(withDensityReal ρ) ≤ q33b_K d ε C₁ a₀ := by
  have hbm : Measurable (fun x : Euc d => q33b_b x y) :=
    (q33b_b_measurable (d := d)).comp (f := fun x : Euc d => (x, y))
      (measurable_id.prodMk measurable_const)
  have hexp : Measurable (fun x : Euc d => Real.exp (ε * q33b_b x y)) :=
    Real.measurable_exp.comp (measurable_const.mul hbm)
  have hind : Measurable (fun z : Euc d =>
      Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) z) :=
    (measurable_norm.pow_const _).indicator measurableSet_ball
  have hindy : Measurable (fun x : Euc d =>
      ENNReal.ofReal (C₁ * (1 + 1 / a₀) *
        Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y))) :=
    ENNReal.measurable_ofReal.comp (((hind.comp (measurable_id.sub_const y))).const_mul _)
  have hΦm : Measurable (fun x : Euc d => ENNReal.ofReal (2 * q33b_Phi C₁ a₀ x)) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    unfold q33b_Phi
    exact measurable_const.mul ((measurable_const.add (measurable_norm.pow_const 2)).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2))))
  have hfm : Measurable (fun x : Euc d => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hm
  have hgm : Measurable (fun x : Euc d => ENNReal.ofReal (Real.exp (ε * q33b_b x y))) :=
    ENNReal.measurable_ofReal.comp hexp
  unfold withDensityReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hfm hgm]
  have hM0 : 0 ≤ C₁ * (1 + 1 / a₀) := mul_nonneg hC (by positivity)
  calc ∫⁻ x, ((fun x => ENNReal.ofReal (ρ x)) * (fun x => ENNReal.ofReal (Real.exp (ε * q33b_b x y)))) x
      ≤ ∫⁻ x, (ENNReal.ofReal (C₁ * (1 + 1 / a₀) *
          Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y))
          + ENNReal.ofReal (2 * q33b_Phi C₁ a₀ x)) := by
        refine lintegral_mono fun x => ?_
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hρ x).1, ← ENNReal.ofReal_add
          (mul_nonneg hM0 (Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) _))
          (mul_nonneg zero_le_two (q33b_Phi_nonneg hC x))]
        apply ENNReal.ofReal_le_ofReal
        have := q33b_pt hε0 hε1 hC ha x y (hρ x).1 (hρ x).2
        linarith
    _ = (∫⁻ x : Euc d, ENNReal.ofReal (C₁ * (1 + 1 / a₀) *
          Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y)))
          + (∫⁻ x : Euc d, ENNReal.ofReal (2 * q33b_Phi C₁ a₀ x)) :=
        lintegral_add_left hindy _
    _ = ENNReal.ofReal (C₁ * (1 + 1 / a₀)) * q33b_loc d ε
          + ENNReal.ofReal 2 * ∫⁻ x : Euc d, ENNReal.ofReal (q33b_Phi C₁ a₀ x) := by
        have h1 : (∫⁻ x : Euc d, ENNReal.ofReal (C₁ * (1 + 1 / a₀) *
            Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) (x - y)))
            = ENNReal.ofReal (C₁ * (1 + 1 / a₀)) * q33b_loc d ε := by
          simp only [ENNReal.ofReal_mul hM0]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          unfold q33b_loc
          exact lintegral_sub_right_eq_self (fun z : Euc d => ENNReal.ofReal
            (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-ε)) z)) y
        have h2 : (∫⁻ x : Euc d, ENNReal.ofReal (2 * q33b_Phi C₁ a₀ x))
            = ENNReal.ofReal 2 * ∫⁻ x : Euc d, ENNReal.ofReal (q33b_Phi C₁ a₀ x) := by
          simp only [ENNReal.ofReal_mul zero_le_two]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [h1, h2]
    _ ≤ q33b_K d ε C₁ a₀ := le_rfl

theorem q33b_K_ne_top {d : ℕ} (hd : 1 ≤ d) {ε C₁ a₀ : ℝ} (hεd : ε < d) (hC : 0 ≤ C₁) (ha : 0 < a₀) :
    q33b_K d ε C₁ a₀ ≠ ⊤ := by
  unfold q33b_K
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (q33b_loc_lt_top hd hεd).ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (q33b_Phi_integrable (d := d) hC ha).lintegral_lt_top.ne⟩

theorem q33b_ell_le {d : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (x : Euc d) :
    ε * q33b_ell x ≤ 1 + ‖x‖ ^ 2 := by
  have hA := q33b_ang_pos x
  have h1 : ε * q33b_ell x = Real.log (q33b_ang x ^ ε) := by
    unfold q33b_ell
    rw [Real.log_rpow hA]
  have h2 : Real.log (q33b_ang x ^ ε) ≤ q33b_ang x ^ ε - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hA ε)
  have h3 := q33b_W_le (d := d) hε0 hε1 x
  linarith [h3.1, h3.2]

theorem q33b_ell_integrable {d : ℕ} {C₁ a₀ ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C₁) (ha : 0 < a₀)
    {ρ : Euc d → ℝ} (hm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) :
    Integrable (fun x : Euc d => q33b_ell x) (withDensityReal ρ) := by
  have hfm : Measurable (fun x : Euc d => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hm
  unfold withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hfm
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hdom : Integrable (fun x : Euc d => (1 / ε) * q33b_Phi C₁ a₀ x) :=
    (q33b_Phi_integrable (d := d) hC ha).const_mul (1 / ε)
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hfm.ennreal_toReal.smul q33b_ell_measurable).aestronglyMeasurable
  · rw [smul_eq_mul, ENNReal.toReal_ofReal (hρ x).1, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ x).1 (q33b_ell_nonneg x))]
    have hΦ : ρ x * (ε * q33b_ell x) ≤ q33b_Phi C₁ a₀ x := by
      unfold q33b_Phi
      calc ρ x * (ε * q33b_ell x) ≤ (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) * (1 + ‖x‖ ^ 2) :=
            mul_le_mul (hρ x).2 (q33b_ell_le hε0 hε1 x) (mul_nonneg hε0.le (q33b_ell_nonneg x))
              (mul_nonneg hC (Real.exp_pos _).le)
        _ = C₁ * ((1 + ‖x‖ ^ 2) * Real.exp (-a₀ * ‖x‖ ^ 2)) := by ring
    have hne : ε ≠ 0 := hε0.ne'
    calc ρ x * q33b_ell x = (1 / ε) * (ρ x * (ε * q33b_ell x)) := by field_simp
      _ ≤ (1 / ε) * q33b_Phi C₁ a₀ x := mul_le_mul_of_nonneg_left hΦ (by positivity)

theorem q33b_prob {d : ℕ} {ρ : Euc d → ℝ} (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hint : ∫ x, ρ x = 1) : IsProbabilityMeasure (withDensityReal ρ) := by
  have hρi : Integrable ρ := by
    by_contra h
    rw [integral_undef h] at hint
    norm_num at hint
  constructor
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρ0), hint,
    ENNReal.ofReal_one]

end HRS.Whole
