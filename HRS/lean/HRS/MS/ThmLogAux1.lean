import HRS.MS.ThmSpecAux2

/-!
# THM-6 (`s = 0`): the shifted logarithmic kernel, the reference density `γ̄`, and (K1)

Namespace `HRS.MS.Thm`; helper lemmas carry the prefix `t67_`.

* `t67l x = log (1 + |x|²)`;
* `t67K d x y = -log |x - y| + ½ t67l x + ½ t67l y + ½ log 2` (the kernel `K̃`): measurable, symmetric, `≥ 0`
  (from `|x-y|² ≤ 2 (1+|x|²)(1+|y|²)`), and `K̃ x y ≤ 1_{|x-y|<1} (-log |x-y|) + C + t67l y`;
* `t67w a β x = exp (β/2 · t67l x - β a |x|²/2) = (1+|x|²)^{β/2} e^{-βa|x|²/2}`, its integral `t67cbar` and the
  normalised density `t67gammaBar = t67w / t67cbar`: probability density, strictly positive, bounded, and
  `t67l · t67gammaBar` integrable;
* `t67_k1`: (K1) for `(K̃, γ̄)`: `y ↦ K̃ x y γ̄ y` is integrable with integral `≤ B`, `B` independent of `x`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

lemma t67_g (z : Euc d) : rieszKernel d 0 z = -Real.log ‖z‖ := by simp [rieszKernel]

lemma t67_g_measurable : Measurable (rieszKernel d 0 : Euc d → ℝ) := by
  have : (rieszKernel d 0 : Euc d → ℝ) = fun z => -Real.log ‖z‖ := funext t67_g
  rw [this]
  exact (Real.measurable_log.comp measurable_norm).neg

/-- `l(x) = log (1 + |x|²)`. -/
def t67l (x : Euc d) : ℝ := Real.log (1 + ‖x‖ ^ 2)

lemma t67l_nonneg (x : Euc d) : 0 ≤ t67l x :=
  Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])

lemma t67l_le_sq (x : Euc d) : t67l x ≤ ‖x‖ ^ 2 := by
  have := Real.log_le_sub_one_of_pos (x := 1 + ‖x‖ ^ 2) (by positivity)
  unfold t67l; linarith

lemma t67l_le {ε : ℝ} (hε : 0 < ε) (x : Euc d) : t67l x ≤ ε * ‖x‖ ^ 2 + (ε - 1 - Real.log ε) := by
  have h1 : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  have := Real.log_le_sub_one_of_pos (x := ε * (1 + ‖x‖ ^ 2)) (by positivity)
  rw [Real.log_mul hε.ne' h1.ne'] at this
  unfold t67l
  linarith

lemma t67l_measurable : Measurable (t67l : Euc d → ℝ) := by
  unfold t67l
  exact Real.measurable_log.comp (measurable_const.add (measurable_norm.pow_const 2))

/-- The kernel `K̃(x,y) = -log |x-y| + ½ log(1+|x|²) + ½ log(1+|y|²) + ½ log 2`. -/
def t67K (d : ℕ) : Euc d → Euc d → ℝ := fun x y =>
  rieszKernel d 0 (x - y) + (1 / 2) * t67l x + (1 / 2) * t67l y + (1 / 2) * Real.log 2

lemma t67_sq_le (x y : Euc d) : ‖x - y‖ ^ 2 ≤ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    gcongr
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖), norm_nonneg x,
    norm_nonneg y]

lemma t67K_measurable : Measurable (Function.uncurry (t67K d)) := by
  have h1 : Measurable fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2) :=
    t67_g_measurable.comp (measurable_fst.sub measurable_snd)
  have h2 : Measurable fun p : Euc d × Euc d => (1 / 2 : ℝ) * t67l p.1 :=
    (t67l_measurable.comp measurable_fst).const_mul _
  have h3 : Measurable fun p : Euc d × Euc d => (1 / 2 : ℝ) * t67l p.2 :=
    (t67l_measurable.comp measurable_snd).const_mul _
  exact ((h1.add h2).add h3).add measurable_const

lemma t67K_symm (x y : Euc d) : t67K d x y = t67K d y x := by
  unfold t67K
  have : x - y = -(y - x) := by abel
  rw [this, t67_g, t67_g, norm_neg]
  ring

lemma t67K_nonneg (x y : Euc d) : 0 ≤ t67K d x y := by
  unfold t67K
  rw [t67_g]
  by_cases h : x - y = 0
  · rw [h]
    simp only [norm_zero, Real.log_zero, neg_zero]
    have := t67l_nonneg x
    have := t67l_nonneg y
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hn : 0 < ‖x - y‖ := norm_pos_iff.2 h
    have h1 := Real.log_le_log (by positivity : 0 < ‖x - y‖ ^ 2) (t67_sq_le x y)
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
      (by positivity)] at h1
    unfold t67l
    push_cast at h1
    linarith

/-- The key one-sided bound: `K̃ x y ≤ 1_{|x-y|<1} (-log |x-y|) + C + l(y)`, `C = ½ log 3 + ½ log 2`. -/
lemma t67K_le (x y : Euc d) :
    t67K d x y ≤ (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) +
      ((1 / 2) * Real.log 3 + (1 / 2) * Real.log 2) + t67l y := by
  have hsq : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), norm_nonneg (x - y), norm_nonneg y, norm_nonneg x]
  by_cases hb : x - y ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hb]
    have hlt : ‖x - y‖ < 1 := by simpa using hb
    have hn0 := norm_nonneg (x - y)
    have h3 : 1 + ‖x‖ ^ 2 ≤ 3 * (1 + ‖y‖ ^ 2) := by nlinarith
    have h4 := Real.log_le_log (by positivity : 0 < 1 + ‖x‖ ^ 2) h3
    rw [Real.log_mul (by norm_num) (by positivity)] at h4
    unfold t67K t67l at *
    linarith
  · rw [Set.indicator_of_notMem hb]
    have hge : 1 ≤ ‖x - y‖ := by
      by_contra hc
      exact hb (by simpa using not_le.1 hc)
    have hn : 0 < ‖x - y‖ := by linarith
    have h3 : 1 + ‖x‖ ^ 2 ≤ 3 * ‖x - y‖ ^ 2 * (1 + ‖y‖ ^ 2) := by
      nlinarith [sq_nonneg ‖y‖, mul_nonneg (sq_nonneg ‖y‖) (sub_nonneg.2 (one_le_pow₀ hge : 1 ≤ ‖x - y‖ ^ 2))]
    have h4 := Real.log_le_log (by positivity : 0 < 1 + ‖x‖ ^ 2) h3
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at h4
    unfold t67K t67l at *
    rw [t67_g]
    push_cast at h4
    linarith

/-! ### The reference density `γ̄` -/

/-- Unnormalised weight `(1+|x|²)^{β/2} e^{-βa|x|²/2} = exp(β/2 · l x - β V x)`. -/
def t67w (a β : ℝ) (x : Euc d) : ℝ := Real.exp (β / 2 * t67l x - β * confinement a x)

/-- Its total mass. -/
def t67cbar (d : ℕ) (a β : ℝ) : ℝ := ∫ x : Euc d, t67w a β x

/-- The normalised reference density `γ̄`. -/
def t67gammaBar (d : ℕ) (a β : ℝ) (x : Euc d) : ℝ := t67w a β x / t67cbar d a β

lemma t67w_pos (a β : ℝ) (x : Euc d) : 0 < t67w a β x := Real.exp_pos _

lemma t67w_measurable (a β : ℝ) : Measurable (t67w a β : Euc d → ℝ) := by
  unfold t67w confinement
  exact Real.measurable_exp.comp
    ((t67l_measurable.const_mul _).sub ((by fun_prop : Measurable fun x : Euc d => a * ‖x‖ ^ 2 / 2).const_mul _))

/-- The Gaussian majorant of `t67w`. -/
lemma t67w_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    t67w a β x ≤ Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) *
      Real.exp (-(β * a / 4) * ‖x‖ ^ 2) := by
  unfold t67w
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := t67l_le (d := d) (ε := a / 2) (by positivity) x
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ β / 2)
  unfold confinement
  nlinarith [h2]

lemma t67w_integrable {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : Integrable (t67w a β : Euc d → ℝ) := by
  have h := (t012_integrable_exp_neg_sq (d := d) (b := β * a / 4) (by positivity)).const_mul
    (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2))
  refine Integrable.mono' h (t67w_measurable a β).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (t67w_pos a β x)]
  exact t67w_le ha hβ x

lemma t67cbar_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : 0 < t67cbar d a β := by
  unfold t67cbar t67w
  exact integral_exp_pos (t67w_integrable (d := d) ha hβ)

lemma t67gammaBar_pos {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) : 0 < t67gammaBar d a β x :=
  div_pos (t67w_pos a β x) (t67cbar_pos ha hβ)

lemma t67gammaBar_measurable (a β : ℝ) : Measurable (t67gammaBar d a β) :=
  (t67w_measurable a β).div_const _

lemma t67gammaBar_integrable {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable (t67gammaBar d a β) :=
  (t67w_integrable ha hβ).div_const _

lemma t67gammaBar_isProbDensity {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsProbDensity (t67gammaBar d a β) where
  nonneg x := (t67gammaBar_pos ha hβ x).le
  measurable := t67gammaBar_measurable a β
  integral_one := by
    unfold t67gammaBar
    rw [integral_div]
    exact div_self (t67cbar_pos ha hβ).ne'

lemma t67gammaBar_le {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    t67gammaBar d a β x ≤ Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) / t67cbar d a β := by
  unfold t67gammaBar
  refine div_le_div_of_nonneg_right ?_ (t67cbar_pos ha hβ).le
  refine (t67w_le ha hβ x).trans ?_
  have : Real.exp (-(β * a / 4) * ‖x‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (β * a / 4) * ‖x‖ ^ 2 := by positivity
    linarith
  calc _ ≤ Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) * 1 :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = _ := mul_one _

/-- `l · γ̄` is integrable. -/
lemma t67_l_gammaBar_integrable {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable fun x : Euc d => t67l x * t67gammaBar d a β x := by
  have h := (t012_integrable_sq_mul_exp (d := d) (b := β * a / 4) (by positivity)).const_mul
    (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) / t67cbar d a β)
  refine Integrable.mono' h
    ((t67l_measurable.mul (t67gammaBar_measurable a β)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  have hc := t67cbar_pos (d := d) ha hβ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (t67l_nonneg x) (t67gammaBar_pos ha hβ x).le)]
  unfold t67gammaBar
  have h1 : t67w a β x / t67cbar d a β ≤
      (Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) * Real.exp (-(β * a / 4) * ‖x‖ ^ 2)) /
        t67cbar d a β := div_le_div_of_nonneg_right (t67w_le ha hβ x) hc.le
  calc t67l x * (t67w a β x / t67cbar d a β)
      ≤ ‖x‖ ^ 2 * ((Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) *
          Real.exp (-(β * a / 4) * ‖x‖ ^ 2)) / t67cbar d a β) :=
        mul_le_mul (t67l_le_sq x) h1 (div_pos (t67w_pos a β x) hc).le (by positivity)
    _ = _ := by ring

/-! ### (K1) -/

lemma t67_ind_integrable (hd : 1 ≤ d) :
    Integrable ((Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0)) := by
  have hloc := rieszKernel_locallyIntegrable (d := d) (s := 0) le_rfl (by exact_mod_cast hd)
  have h1 : IntegrableOn (rieszKernel d 0) (Metric.closedBall (0 : Euc d) 1) :=
    hloc.integrableOn_isCompact (isCompact_closedBall _ _)
  have h2 : IntegrableOn (rieszKernel d 0) (Metric.ball (0 : Euc d) 1) :=
    h1.mono_set Metric.ball_subset_closedBall
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 h2

lemma t67_ind_nonneg (z : Euc d) : 0 ≤ (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z := by
  by_cases hb : z ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hb, t67_g]
    have hlt : ‖z‖ < 1 := by simpa using hb
    by_cases h0 : z = 0
    · simp [h0]
    · have := Real.log_nonpos (norm_nonneg z) hlt.le
      linarith
  · rw [Set.indicator_of_notMem hb]

/-- **(K1) for `(K̃, γ̄)`.** -/
theorem t67_k1 (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ B : ℝ, ∀ x : Euc d, Integrable (fun y => t67K d x y * t67gammaBar d a β y) ∧
      ∫ y, t67K d x y * t67gammaBar d a β y ≤ B := by
  set S : ℝ := Real.exp (β * (a / 2 - 1 - Real.log (a / 2)) / 2) / t67cbar d a β with hS
  set C : ℝ := (1 / 2) * Real.log 3 + (1 / 2) * Real.log 2 with hC
  set I : ℝ := ∫ z, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z with hI
  set J : ℝ := ∫ y, t67l y * t67gammaBar d a β y with hJ
  have hint := t67_ind_integrable (d := d) hd
  have hγi := t67gammaBar_integrable (d := d) ha hβ
  have hγm := t67gammaBar_measurable (d := d) a β
  have hlγ := t67_l_gammaBar_integrable (d := d) ha hβ
  have hS0 : 0 ≤ S := by
    have := t67gammaBar_pos (d := d) ha hβ 0
    exact this.le.trans (t67gammaBar_le ha hβ 0)
  refine ⟨S * I + C + J, fun x => ?_⟩
  -- the majorant
  have h1 : Integrable fun y : Euc d =>
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y := by
    have := (hint.comp_sub_left x)
    refine this.mul_bdd (c := S) hγm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (t67gammaBar_pos ha hβ y)]
    exact t67gammaBar_le ha hβ y
  have h1' : Integrable fun y : Euc d =>
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y := h1
  have h2 : Integrable fun y : Euc d => C * t67gammaBar d a β y := hγi.const_mul C
  have hmaj : Integrable fun y : Euc d =>
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y := (h1'.add h2).add hlγ
  have hmeasK : Measurable fun y : Euc d => t67K d x y * t67gammaBar d a β y :=
    ((t67K_measurable.comp (measurable_const.prodMk measurable_id))).mul hγm
  have hle : ∀ y, ‖t67K d x y * t67gammaBar d a β y‖ ≤
      (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y := by
    intro y
    have hp := t67gammaBar_pos (d := d) ha hβ y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (t67K_nonneg x y) hp.le)]
    have := t67K_le x y
    nlinarith [mul_le_mul_of_nonneg_right this hp.le]
  have hKint : Integrable fun y : Euc d => t67K d x y * t67gammaBar d a β y :=
    Integrable.mono' hmaj hmeasK.aestronglyMeasurable (ae_of_all _ hle)
  refine ⟨hKint, ?_⟩
  calc ∫ y, t67K d x y * t67gammaBar d a β y
      ≤ ∫ y, ((Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
        C * t67gammaBar d a β y + t67l y * t67gammaBar d a β y) := by
        refine integral_mono hKint hmaj fun y => ?_
        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hle y)
    _ = (∫ y, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y) +
        C * (∫ y, t67gammaBar d a β y) + J := by
        have hAB : Integrable fun y : Euc d =>
            (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) * t67gammaBar d a β y +
              C * t67gammaBar d a β y := h1'.add h2
        rw [integral_add hAB hlγ, integral_add h1' h2, integral_const_mul]
    _ ≤ S * I + C + J := by
        have hb : ∫ y, (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) *
            t67gammaBar d a β y ≤ ∫ y, S * (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) := by
          refine integral_mono h1' ((hint.comp_sub_left x).const_mul S) fun y => ?_
          have := t67_ind_nonneg (d := d) (x - y)
          nlinarith [t67gammaBar_le ha hβ y]
        have hc : ∫ y, S * (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) (x - y) = S * I := by
          rw [integral_const_mul]
          congr 1
          exact integral_sub_left_eq_self (fun z => (Metric.ball (0 : Euc d) 1).indicator (rieszKernel d 0) z)
            volume x
        have hone : ∫ y, t67gammaBar d a β y = 1 := (t67gammaBar_isProbDensity (d := d) ha hβ).integral_one
        have e : C * (∫ y, t67gammaBar d a β y) = C := by rw [hone, mul_one]
        rw [e]
        have h3 := hb.trans hc.le
        linarith

end HRS.MS.Thm

end
