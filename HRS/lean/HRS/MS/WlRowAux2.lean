import HRS.MS.WlRowAux1

/-!
# WL-2 (part 2): row moments, tail, `q_M` row bound and the Schur bound (S3.5 infrastructure)

Namespace `HRS.MS.Wl`, helper prefix `wl2_`.  Hypotheses throughout: `2 ≤ d`, `IsProbDensity ρ`,
`HasSphericalBound A ρ` (a.e.), `μ = withDensityReal ρ`; constants `∃ C` are quantified before `ρ` and
are uniform in `x`.  All integral bounds are derived from the level-set lemma `wl_level_enn` of
`WlRowAux1` by the layer-cake formula `lintegral_comp_eq_lintegral_meas_lt_mul` (so, in contrast to
the sketch in `docs/WR_LOG_PLAN.md`, `t67K_le` is not needed).

* `wl_row_pow p` : `Integrable (K x ·^p) μ ∧ ∫ K x y ^ p dμ ≤ C`;
* `wl_row_tail`  : for `L ≥ 1`, `K x ·` is integrable on `{K x · > L}` and the integral is `≤ C (1+L) e^{-dL}`;
* `wl_row_qm`    : `wl2_qm M x y = ∑' j, ½ τ^{M+1+j}/(M+1+j)` with `τ = 1 - |x-y|²/((1+|x|²)(1+|y|²))`
  (the same `τ` as WL-1's `(1 + ⟨u x, u y⟩)/2` by `1 - τ = |x-y|²/((1+|x|²)(1+|y|²))`; the `tsum` is
  junk-safe: at `x = y` it is `0`, and `qm ≥ 0` everywhere); `∫ qm M x y dμ ≤ C M^{-d/2}` for `M ≥ 1`;
* `wl_schur`     : `|h| ≤ B (1+K)` off the diagonal gives `∫ |h x y| dμ ≤ C B`, `∫ |h x y|² dμ ≤ C B²`
  and `Integrable h (μ.prod μ)`; no sign hypothesis on `B` is needed (`B ≥ 0` is derived, and `B = 0`
  gives `0`).
-/

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole

variable {d : ℕ}

/-! ### Layer cake -/

lemma wl2_lc {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] {f : α → ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hfm : Measurable f) {g H : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t, 0 < t → 0 ≤ g t) (hH0 : ∀ t, 0 < t → 0 ≤ H t)
    (hμ : ∀ t, 0 < t → μ {a | t < f a} ≤ ENNReal.ofReal (H t)) :
    ∫⁻ a, ENNReal.ofReal (∫ t in (0 : ℝ)..f a, g t) ∂μ ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (H t * g t) := by
  rw [lintegral_comp_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hf0) hfm.aemeasurable
    (fun t _ => hg.intervalIntegrable _ _)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => hg0 t ht))]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [ENNReal.ofReal_mul (hH0 t ht)]
  exact mul_le_mul' (hμ t ht) le_rfl

lemma wl2_integrableOn_pow_exp (hd : 1 ≤ d) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(d : ℝ) * t)) (Ioi 0) := by
  have hb : (0 : ℝ) < d := by exact_mod_cast hd
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := d)
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hb
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

lemma wl2_ofReal_setIntegral {F : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hF : IntegrableOn F S)
    (hF0 : ∀ t ∈ S, 0 ≤ F t) :
    ∫⁻ t in S, ENNReal.ofReal (F t) = ENNReal.ofReal (∫ t in S, F t) :=
  (ofReal_integral_eq_lintegral_ofReal hF ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hF0))).symm


/-! ### Row moments -/

lemma wl2_row_pow_succ (hd : 1 ≤ d) (n : ℕ) {Cl : ℝ} (hCl : 0 ≤ Cl) {μ : Measure (Euc d)}
    [SFinite μ] (x : Euc d)
    (hlev : ∀ L : ℝ, 0 ≤ L → μ {y | L < sphericalLogKernel x y} ≤
      ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L))) :
    ∫⁻ y, ENNReal.ofReal (sphericalLogKernel x y ^ (n + 1)) ∂μ ≤
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (Cl * Real.exp (-(d : ℝ) * t)) * (((n : ℝ) + 1) * t ^ n)) := by
  have h := wl2_lc μ (f := sphericalLogKernel x) (HRS.MS.Comm.comm_log_nonneg x) (wl2_K_measurable_right x)
    (g := fun t => ((n : ℝ) + 1) * t ^ n) (H := fun t => Cl * Real.exp (-(d : ℝ) * t))
    (by fun_prop) (fun t ht => by positivity) (fun t ht => by positivity)
    (fun t ht => hlev t ht.le)
  have heq : ∀ a : ℝ, ∫ t in (0 : ℝ)..a, ((n : ℝ) + 1) * t ^ n = a ^ (n + 1) := by
    intro a
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    simp
  simp only [heq] at h
  refine h.trans (le_of_eq ?_)
  have hint : IntegrableOn (fun t : ℝ => (Cl * Real.exp (-(d : ℝ) * t)) * (((n : ℝ) + 1) * t ^ n)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ => (Cl * ((n : ℝ) + 1)) * (t ^ n * Real.exp (-(d : ℝ) * t))) (Ioi 0) :=
      (wl2_integrableOn_pow_exp hd n).const_mul _
    exact h1.congr_fun (fun t _ => by ring) measurableSet_Ioi
  exact wl2_ofReal_setIntegral measurableSet_Ioi hint (fun t ht => by
    have : 0 < t := ht
    positivity)

/-- **`wl_row_pow`.**  Row moments of `K`, uniform in `x`. -/
theorem wl_row_pow (hd : 2 ≤ d) (A : ℝ) (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ x : Euc d,
      Integrable (fun y => sphericalLogKernel x y ^ p) (HRS.Whole.withDensityReal ρ) ∧
        ∫ y, sphericalLogKernel x y ^ p ∂(HRS.Whole.withDensityReal ρ) ≤ C := by
  obtain ⟨Cl, hCl0, hCl⟩ := wl_level_enn hd A
  cases p with
  | zero =>
    refine ⟨1, zero_le_one, fun ρ hρ hA x => ?_⟩
    haveI := wl2_isProb hρ
    simp
  | succ n =>
    refine ⟨∫ t in Ioi (0 : ℝ), (Cl * Real.exp (-(d : ℝ) * t)) * (((n : ℝ) + 1) * t ^ n),
      setIntegral_nonneg measurableSet_Ioi (fun t ht => by
        have : 0 < t := ht
        positivity), fun ρ hρ hA x => ?_⟩
    haveI := wl2_isProb hρ
    refine wl2_integrable_of_lintegral_le ((wl2_K_measurable_right x).pow_const _).aemeasurable
      (fun y => pow_nonneg (HRS.MS.Comm.comm_log_nonneg x y) _) (setIntegral_nonneg measurableSet_Ioi (fun t ht => by
        have : 0 < t := ht
        positivity)) ?_
    exact wl2_row_pow_succ (by omega) n hCl0 x (fun L hL => hCl ρ hρ hA x L hL)


/-! ### Tail of the row -/

/-- `∫_0^∞ e^{-d t} dt` (kept as an integral; only finiteness and nonnegativity matter). -/
def wl2_Ie (d : ℕ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-(d : ℝ) * t)

lemma wl2_Ie_nonneg (d : ℕ) : 0 ≤ wl2_Ie d :=
  setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le

lemma wl2_integrableOn_exp (hd : 1 ≤ d) :
    IntegrableOn (fun t : ℝ => Real.exp (-(d : ℝ) * t)) (Ioi 0) := by
  simpa using wl2_integrableOn_pow_exp hd 0

lemma wl2_tail_lintegral (hd : 1 ≤ d) {Cl : ℝ} (hCl : 0 ≤ Cl) {μ : Measure (Euc d)} [SFinite μ]
    (x : Euc d) {L : ℝ} (hL : 0 ≤ L)
    (hlev : ∀ L : ℝ, 0 ≤ L → μ {y | L < sphericalLogKernel x y} ≤
      ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L))) :
    ∫⁻ y, ENNReal.ofReal ({y | L < sphericalLogKernel x y}.indicator (sphericalLogKernel x) y) ∂μ ≤
      ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L) * (wl2_Ie d + L)) := by
  set S : Set (Euc d) := {y | L < sphericalLogKernel x y} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (wl2_K_measurable_right x)
  set f : Euc d → ℝ := fun y => max (sphericalLogKernel x y - L) 0 with hf
  have hfm : Measurable f := ((wl2_K_measurable_right x).sub_const L).max measurable_const
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_right _ _
  have h1 := wl2_lc μ hf0 hfm (g := fun _ => (1 : ℝ))
    (H := fun t => Cl * Real.exp (-(d : ℝ) * (L + t))) continuous_const (fun _ _ => zero_le_one)
    (fun t ht => by positivity) (fun t ht => by
      refine (measure_mono ?_).trans (hlev (L + t) (by linarith))
      intro y hy
      have hy' : t < f y := hy
      have : t < sphericalLogKernel x y - L := by
        rcases le_total (sphericalLogKernel x y - L) 0 with h | h
        · have : f y = 0 := by simp only [hf]; exact max_eq_right h
          linarith
        · have : f y = sphericalLogKernel x y - L := by simp only [hf]; exact max_eq_left h
          linarith
      show L + t < sphericalLogKernel x y
      linarith)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * (L + t))) =
      ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L) * wl2_Ie d) := by
    have hfun : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * (L + t))) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((Cl * Real.exp (-(d : ℝ) * L)) * Real.exp (-(d : ℝ) * t)) := by
      refine lintegral_congr fun t => ?_
      congr 1
      rw [mul_add, Real.exp_add]; ring
    rw [hfun, wl2_ofReal_setIntegral measurableSet_Ioi ((wl2_integrableOn_exp hd).const_mul _)
      (fun t _ => by positivity), integral_const_mul]
    rfl
  have hpt : ∀ y, ENNReal.ofReal (S.indicator (sphericalLogKernel x) y) ≤
      ENNReal.ofReal (f y) + S.indicator (fun _ => ENNReal.ofReal L) y := by
    intro y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      have : sphericalLogKernel x y = f y + L := by
        have hh : L < sphericalLogKernel x y := hy
        simp only [hf]; rw [max_eq_left (by linarith)]; ring
      rw [this]
      exact ENNReal.ofReal_add_le
    · rw [Set.indicator_of_notMem hy]; simp
  calc ∫⁻ y, ENNReal.ofReal (S.indicator (sphericalLogKernel x) y) ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal (f y) + S.indicator (fun _ => ENNReal.ofReal L) y) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ y, ENNReal.ofReal (f y) ∂μ + ENNReal.ofReal L * μ S := by
        have hm : Measurable (fun y => ENNReal.ofReal (f y)) := ENNReal.measurable_ofReal.comp hfm
        rw [lintegral_add_left hm, lintegral_indicator_const hSm]
    _ ≤ ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L) * wl2_Ie d) +
          ENNReal.ofReal L * ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L)) := by
        refine add_le_add (h1.trans (le_of_eq h2)) (mul_le_mul' le_rfl (hlev L hL))
    _ = ENNReal.ofReal (Cl * Real.exp (-(d : ℝ) * L) * (wl2_Ie d + L)) := by
        rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_add (by have := wl2_Ie_nonneg d; positivity)
          (by positivity)]
        congr 1; ring

/-- **`wl_row_tail`.**  `∫_{K>L} K dμ ≤ C (1+L) e^{-dL}` for `L ≥ 1`. -/
theorem wl_row_tail (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ (x : Euc d) (L : ℝ), 1 ≤ L →
      IntegrableOn (sphericalLogKernel x) {y | L < sphericalLogKernel x y} (HRS.Whole.withDensityReal ρ) ∧
        ∫ y in {y | L < sphericalLogKernel x y}, sphericalLogKernel x y ∂(HRS.Whole.withDensityReal ρ) ≤
          C * (1 + L) * Real.exp (-(d : ℝ) * L) := by
  obtain ⟨Cl, hCl0, hCl⟩ := wl_level_enn hd A
  refine ⟨Cl * (wl2_Ie d + 1), by have := wl2_Ie_nonneg d; positivity, fun ρ hρ hA x L hL => ?_⟩
  haveI := wl2_isProb hρ
  have hL0 : 0 ≤ L := by linarith
  have hSm : MeasurableSet {y | L < sphericalLogKernel x y} :=
    measurableSet_lt measurable_const (wl2_K_measurable_right x)
  have hbd := wl2_tail_lintegral (by omega) hCl0 x hL0 (fun L hL => hCl ρ hρ hA x L hL)
  have hC0 : 0 ≤ Cl * Real.exp (-(d : ℝ) * L) * (wl2_Ie d + L) := by
    have := wl2_Ie_nonneg d; positivity
  have key := wl2_integrable_of_lintegral_le
    ((wl2_K_measurable_right x).indicator hSm).aemeasurable
    (fun y => Set.indicator_nonneg (fun y _ => HRS.MS.Comm.comm_log_nonneg x y) y) hC0 hbd
  refine ⟨(integrable_indicator_iff hSm).1 key.1, ?_⟩
  rw [← integral_indicator hSm]
  refine key.2.trans ?_
  have := wl2_Ie_nonneg d
  have hex := Real.exp_pos (-(d : ℝ) * L)
  nlinarith [mul_nonneg hCl0 hex.le, mul_nonneg (mul_nonneg hCl0 hex.le) this]


/-! ### The chordal quantity and the exponential moment -/

/-- Squared chordal distance `c(x,y) = |x-y|² / ((1+|x|²)(1+|y|²))`. -/
def wl2_c (x y : Euc d) : ℝ := ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))

/-- `τ = 1 - c` (`= (1 + ⟨u x, u y⟩)/2` for the inverse stereographic projection `u`). -/
def wl2_tau (x y : Euc d) : ℝ := 1 - wl2_c x y

lemma wl2_c_nonneg (x y : Euc d) : 0 ≤ wl2_c x y := by unfold wl2_c; positivity

lemma wl2_c_le_one (x y : Euc d) : wl2_c x y ≤ 1 := by
  unfold wl2_c
  rw [div_le_one (by positivity)]
  have h1 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x‖ * ‖y‖ - 1)]

lemma wl2_tau_nonneg (x y : Euc d) : 0 ≤ wl2_tau x y := by
  unfold wl2_tau; linarith [wl2_c_le_one x y]

lemma wl2_tau_le_one (x y : Euc d) : wl2_tau x y ≤ 1 := by
  unfold wl2_tau; linarith [wl2_c_nonneg x y]

lemma wl2_c_measurable_right (x : Euc d) : Measurable (wl2_c x) := by
  unfold wl2_c
  have h1 : Measurable fun y : Euc d => ‖x - y‖ ^ 2 :=
    (measurable_norm.comp (measurable_const.sub measurable_id)).pow_const 2
  have h2 : Measurable fun y : Euc d => (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) :=
    measurable_const.mul (measurable_const.add (measurable_norm.pow_const 2))
  exact h1.div h2

lemma wl2_c_measurable : Measurable (fun p : Euc d × Euc d => wl2_c p.1 p.2) := by
  unfold wl2_c
  have h1 : Measurable fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ 2 :=
    (measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const 2
  have h2 : Measurable fun p : Euc d × Euc d => (1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2) :=
    (measurable_const.add ((measurable_norm.comp measurable_fst).pow_const 2)).mul
      (measurable_const.add ((measurable_norm.comp measurable_snd).pow_const 2))
  exact h1.div h2

lemma wl2_sqrt_pow_le (hd : 1 ≤ d) {u j : ℝ} (hu : 0 ≤ u) (hj : 0 < j) :
    (Real.sqrt (u / j)) ^ d ≤
      (1 + 2 ^ d * (d.factorial : ℝ) * Real.exp (u / 2)) / (Real.sqrt j) ^ d := by
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.2 hj
  rw [Real.sqrt_div hu, div_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  set w := Real.sqrt u with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hww : w ^ 2 = u := Real.sq_sqrt hu
  have hexp : u ^ d ≤ 2 ^ d * (d.factorial : ℝ) * Real.exp (u / 2) := by
    have h := Real.pow_div_factorial_le_exp (u / 2) (by positivity) d
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    rw [div_le_iff₀ hf, div_pow] at h
    have h2 : (0 : ℝ) < 2 ^ d := by positivity
    rw [div_le_iff₀ h2] at h
    nlinarith
  by_cases hw1 : w ≤ 1
  · have : w ^ d ≤ 1 := pow_le_one₀ hw0 hw1
    have h3 : 0 ≤ 2 ^ d * (d.factorial : ℝ) * Real.exp (u / 2) := by positivity
    linarith
  · push Not at hw1
    have : w ^ d ≤ w ^ (2 * d) := pow_le_pow_right₀ hw1.le (by omega)
    have h4 : w ^ (2 * d) = u ^ d := by rw [pow_mul, hww]
    linarith [h4]

lemma wl2_exp_at_log {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.log t / 2) = t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos ht]; congr 1; ring


lemma wl2_int_exp1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 0) (b := 1) (by norm_num) one_pos one_pos
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

lemma wl2_int_sqrt : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-t)) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := 1) (by norm_num)
    one_pos one_pos
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

/-- The dominating function of the exponential moment. -/
def wl2_Fe (d : ℕ) (t : ℝ) : ℝ :=
  Real.exp 1 * (1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ))) * Real.exp (-t)

lemma wl2_Fe_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ wl2_Fe d t := by
  unfold wl2_Fe
  have : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  positivity

lemma wl2_Fe_integrableOn (d : ℕ) : IntegrableOn (wl2_Fe d) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp 1 * Real.exp (-t) +
      (Real.exp 1 * (2 ^ d * (d.factorial : ℝ))) * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-t))) (Ioi 0) :=
    (wl2_int_exp1.const_mul _).add (wl2_int_sqrt.const_mul _)
  refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioi
  unfold wl2_Fe
  ring

lemma wl2_exp_moment_lintegral (hd : 1 ≤ d) {Cb : ℝ} (hCb : 0 ≤ Cb) {μ : Measure (Euc d)} [SFinite μ]
    (x : Euc d)
    (hch : ∀ δ : ℝ, 0 < δ → μ {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} ≤
      ENNReal.ofReal (Cb * δ ^ d)) (j : ℕ) (hj : 1 ≤ j) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-(j : ℝ) * wl2_c x y)) ∂μ ≤
      ENNReal.ofReal (Cb * (∫ t in Ioi (0 : ℝ), wl2_Fe d t) / (Real.sqrt j) ^ d) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hj0
  set J' : ℝ := (Real.sqrt (j : ℝ)) ^ d with hJ'
  have hJ'0 : 0 < J' := by positivity
  set f : Euc d → ℝ := fun y => Real.exp (-(j : ℝ) * wl2_c x y) with hf
  have hfm : Measurable f :=
    Real.measurable_exp.comp (measurable_const.mul (wl2_c_measurable_right x))
  have hf0 : ∀ y, 0 ≤ f y := fun y => (Real.exp_pos _).le
  have hf1 : ∀ y, f y ≤ 1 := fun y => by
    simp only [hf]
    rw [Real.exp_le_one_iff]
    have := wl2_c_nonneg x y
    nlinarith
  have h1 := wl2_lc μ hf0 hfm (g := fun _ => (1 : ℝ))
    (H := fun t => Cb * (Real.sqrt (-Real.log t / j)) ^ d) continuous_const (fun _ _ => zero_le_one)
    (fun t ht => by positivity) (fun t ht => by
      by_cases ht1 : 1 ≤ t
      · have : {a | t < f a} = ∅ := by
          ext y
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
          exact (hf1 y).trans ht1
        rw [this, measure_empty]
        exact zero_le
      · push Not at ht1
        have hu : 0 < -Real.log t := by linarith [Real.log_neg ht ht1]
        have hδ : 0 < Real.sqrt (-Real.log t / j) := Real.sqrt_pos.2 (by positivity)
        refine le_trans (measure_mono ?_) (hch _ hδ)
        intro y hy
        have hy' : t < f y := hy
        show ‖x - y‖ ^ 2 ≤ (Real.sqrt (-Real.log t / j)) ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))
        rw [Real.sq_sqrt (by positivity)]
        have hlog : Real.log t < -(j : ℝ) * wl2_c x y := by
          have := Real.log_lt_log ht hy'
          simpa [hf, Real.log_exp] using this
        have hP : 0 < (1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) := by positivity
        have hc : wl2_c x y * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) = ‖x - y‖ ^ 2 := by
          unfold wl2_c; field_simp
        rw [← hc]
        apply mul_le_mul_of_nonneg_right _ hP.le
        rw [le_div_iff₀ hj0]
        nlinarith)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
  refine h1.trans ?_
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (Cb * (Real.sqrt (-Real.log t / j)) ^ d) ≤
      ENNReal.ofReal ((Cb / J') * wl2_Fe d t) := by
    intro t ht
    have ht0 : 0 < t := ht
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht1 : 1 ≤ t
    · have : -Real.log t / j ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_nonneg ht1]) hj0.le
      rw [Real.sqrt_eq_zero_of_nonpos this, zero_pow (by omega), mul_zero]
      exact mul_nonneg (by positivity) (wl2_Fe_nonneg d ht0)
    · push Not at ht1
      have hu : 0 < -Real.log t := by linarith [Real.log_neg ht0 ht1]
      have h2 := wl2_sqrt_pow_le hd hu.le hj0
      rw [show -Real.log t / 2 = -Real.log t / 2 from rfl, wl2_exp_at_log ht0] at h2
      have h3 : 1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ)) ≤ wl2_Fe d t := by
        unfold wl2_Fe
        have hq : 0 ≤ 1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
          have : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
          positivity
        have : 1 ≤ Real.exp 1 * Real.exp (-t) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
        calc 1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ))
            = (1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ))) * 1 := by ring
          _ ≤ (1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ))) * (Real.exp 1 * Real.exp (-t)) :=
              mul_le_mul_of_nonneg_left this hq
          _ = _ := by ring
      calc Cb * (Real.sqrt (-Real.log t / j)) ^ d
          ≤ Cb * ((1 + 2 ^ d * (d.factorial : ℝ) * t ^ (-(1 / 2 : ℝ))) / J') :=
            mul_le_mul_of_nonneg_left h2 hCb
        _ ≤ Cb * (wl2_Fe d t / J') :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 hJ'0.le) hCb
        _ = _ := by ring
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Cb * (Real.sqrt (-Real.log t / j)) ^ d)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((Cb / J') * wl2_Fe d t) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (Cb / J') * wl2_Fe d t) :=
        wl2_ofReal_setIntegral measurableSet_Ioi ((wl2_Fe_integrableOn d).const_mul _)
          (fun t ht => mul_nonneg (by positivity) (wl2_Fe_nonneg d ht))
    _ = _ := by rw [integral_const_mul]; congr 1; ring


/-! ### A tail sum -/

lemma wl2_b_le {α : ℝ} (hα : 1 ≤ α) {q : ℕ} (hq : 1 ≤ q) :
    ((((q + 1 : ℕ) : ℝ) ^ α) * ((q + 1 : ℕ) : ℝ))⁻¹ ≤
      (1 / α) * (((q : ℝ) ^ α)⁻¹ - ((((q + 1 : ℕ) : ℝ) ^ α)⁻¹)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hα0 : 0 < α := by linarith
  have hB := one_add_mul_self_le_rpow_one_add (s := 1 / (q : ℝ)) (by
    have : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    linarith) hα
  have hrat : (1 + 1 / (q : ℝ)) = ((q + 1 : ℕ) : ℝ) / q := by
    push_cast; field_simp
  rw [hrat, Real.div_rpow hq1.le hq0.le] at hB
  have hqa : 0 < (q : ℝ) ^ α := Real.rpow_pos_of_pos hq0 _
  have hqa1 : 0 < ((q + 1 : ℕ) : ℝ) ^ α := Real.rpow_pos_of_pos hq1 _
  have h1 : α / ((q + 1 : ℕ) : ℝ) ≤ α * (1 / (q : ℝ)) := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hα0.le hq0
    push_cast; linarith
  have h2 : α / ((q + 1 : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) ^ α / (q : ℝ) ^ α - 1 := by linarith
  have h3 : α / ((q + 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) ^ α)⁻¹ ≤
      (((q + 1 : ℕ) : ℝ) ^ α / (q : ℝ) ^ α - 1) * (((q + 1 : ℕ) : ℝ) ^ α)⁻¹ :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have e1 : (((q + 1 : ℕ) : ℝ) ^ α / (q : ℝ) ^ α - 1) * (((q + 1 : ℕ) : ℝ) ^ α)⁻¹ =
      ((q : ℝ) ^ α)⁻¹ - (((q + 1 : ℕ) : ℝ) ^ α)⁻¹ := by
    field_simp
  rw [e1] at h3
  have e2 : (((q + 1 : ℕ) : ℝ) ^ α * ((q + 1 : ℕ) : ℝ))⁻¹ =
      (1 / α) * (α / ((q + 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) ^ α)⁻¹) := by
    field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

lemma wl2_sum_tail {α : ℝ} (hα : 1 ≤ α) {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((((M + 1 + i : ℕ) : ℝ) ^ α) * ((M + 1 + i : ℕ) : ℝ))⁻¹ ≤
      (1 / α) * (((M : ℝ) ^ α)⁻¹) := by
  have hα0 : 0 < α := by linarith
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((((M + 1 + i : ℕ) : ℝ) ^ α) * ((M + 1 + i : ℕ) : ℝ))⁻¹ ≤
      (1 / α) * (((M : ℝ) ^ α)⁻¹) - (1 / α) * ((((M + N : ℕ) : ℝ) ^ α)⁻¹) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := wl2_b_le hα (q := M + n) (by omega)
      have e : M + 1 + n = M + n + 1 := by ring
      have e' : M + (n + 1) = M + n + 1 := by ring
      rw [e, e']
      push_cast at h ih ⊢
      linarith
  refine (key N).trans ?_
  have : 0 ≤ (1 / α) * ((((M + N : ℕ) : ℝ) ^ α)⁻¹) := by positivity
  linarith


/-! ### The tail kernel `q_M` and its row bound -/

/-- The `j`-th term `½ τ^{M+1+j} / (M+1+j)` of the tail series of `K`. -/
def wl2_qterm (M : ℕ) (x y : Euc d) (j : ℕ) : ℝ :=
  (1 / 2) * wl2_tau x y ^ (M + 1 + j) / ((M + 1 + j : ℕ) : ℝ)

/-- The tail kernel `q_M(x,y) = ½ ∑_{j > M} τ^j/j` as a real `tsum` (junk-safe: nonnegative everywhere, `0`
at `x = y` where the series diverges). -/
def wl2_qm (M : ℕ) (x y : Euc d) : ℝ := ∑' j : ℕ, wl2_qterm M x y j

lemma wl2_qterm_nonneg (M : ℕ) (x y : Euc d) (j : ℕ) : 0 ≤ wl2_qterm M x y j := by
  unfold wl2_qterm
  have := wl2_tau_nonneg x y
  positivity

lemma wl2_qm_nonneg (M : ℕ) (x y : Euc d) : 0 ≤ wl2_qm M x y :=
  tsum_nonneg (wl2_qterm_nonneg M x y)

lemma wl2_qm_eq (M : ℕ) (x y : Euc d) :
    wl2_qm M x y = (∑' j : ℕ, ENNReal.ofReal (wl2_qterm M x y j)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
  unfold wl2_qm
  exact tsum_congr fun j => (ENNReal.toReal_ofReal (wl2_qterm_nonneg M x y j)).symm

lemma wl2_qterm_measurable_right (M : ℕ) (x : Euc d) (j : ℕ) :
    Measurable fun y => wl2_qterm M x y j := by
  unfold wl2_qterm wl2_tau
  exact (((measurable_const.sub (wl2_c_measurable_right x)).pow_const _).const_mul _).div_const _

lemma wl2_qm_measurable_right (M : ℕ) (x : Euc d) : Measurable (wl2_qm M x) := by
  have : wl2_qm M x = fun y => (∑' j : ℕ, ENNReal.ofReal (wl2_qterm M x y j)).toReal :=
    funext (wl2_qm_eq M x)
  rw [this]
  exact (Measurable.ennreal_tsum fun j =>
    ENNReal.measurable_ofReal.comp (wl2_qterm_measurable_right M x j)).ennreal_toReal

lemma wl2_ofReal_qm_le (M : ℕ) (x y : Euc d) :
    ENNReal.ofReal (wl2_qm M x y) ≤ ∑' j : ℕ, ENNReal.ofReal (wl2_qterm M x y j) := by
  rw [wl2_qm_eq]
  exact ENNReal.ofReal_toReal_le

lemma wl2_tau_pow_le (x y : Euc d) (k : ℕ) :
    wl2_tau x y ^ k ≤ Real.exp (-(k : ℝ) * wl2_c x y) := by
  have h1 : wl2_tau x y ≤ Real.exp (-wl2_c x y) := by
    unfold wl2_tau; exact Real.one_sub_le_exp_neg _
  calc wl2_tau x y ^ k ≤ (Real.exp (-wl2_c x y)) ^ k := pow_le_pow_left₀ (wl2_tau_nonneg x y) h1 k
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma wl2_sqrt_pow_eq (d : ℕ) {y : ℝ} (hy : 0 ≤ y) : (Real.sqrt y) ^ d = y ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  congr 1; ring

lemma wl2_term_lintegral (hd : 2 ≤ d) {Cb : ℝ} (hCb : 0 ≤ Cb) {μ : Measure (Euc d)} [SFinite μ]
    (x : Euc d)
    (hch : ∀ δ : ℝ, 0 < δ → μ {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} ≤
      ENNReal.ofReal (Cb * δ ^ d)) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ y, ENNReal.ofReal ((1 / 2) * wl2_tau x y ^ k / (k : ℝ)) ∂μ ≤
      ENNReal.ofReal ((Cb * (∫ t in Ioi (0 : ℝ), wl2_Fe d t) / 2) *
        ((((k : ℝ) ^ ((d : ℝ) / 2)) * (k : ℝ))⁻¹)) := by
  set Ke : ℝ := ∫ t in Ioi (0 : ℝ), wl2_Fe d t with hKe
  have hKe0 : 0 ≤ Ke := setIntegral_nonneg measurableSet_Ioi fun t ht => wl2_Fe_nonneg d ht
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := wl2_exp_moment_lintegral (by omega) hCb x hch k hk
  rw [wl2_sqrt_pow_eq d hk0.le] at h1
  have hm : Measurable fun y => ENNReal.ofReal (Real.exp (-(k : ℝ) * wl2_c x y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (wl2_c_measurable_right x)))
  calc ∫⁻ y, ENNReal.ofReal ((1 / 2) * wl2_tau x y ^ k / (k : ℝ)) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal (1 / (2 * (k : ℝ))) * ENNReal.ofReal (Real.exp (-(k : ℝ) * wl2_c x y)) ∂μ := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := wl2_tau_pow_le x y k
        have e : (1 / 2) * wl2_tau x y ^ k / (k : ℝ) = (1 / (2 * (k : ℝ))) * wl2_tau x y ^ k := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = ENNReal.ofReal (1 / (2 * (k : ℝ))) * ∫⁻ y, ENNReal.ofReal (Real.exp (-(k : ℝ) * wl2_c x y)) ∂μ :=
        lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (1 / (2 * (k : ℝ))) *
          ENNReal.ofReal (Cb * Ke / (k : ℝ) ^ ((d : ℝ) / 2)) := mul_le_mul' le_rfl h1
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : (k : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hk0 _).ne'
        field_simp

lemma wl2_qm_lintegral (hd : 2 ≤ d) {Cb : ℝ} (hCb : 0 ≤ Cb) {μ : Measure (Euc d)} [SFinite μ]
    (x : Euc d)
    (hch : ∀ δ : ℝ, 0 < δ → μ {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} ≤
      ENNReal.ofReal (Cb * δ ^ d)) {M : ℕ} (hM : 1 ≤ M) :
    ∫⁻ y, ENNReal.ofReal (wl2_qm M x y) ∂μ ≤
      ENNReal.ofReal ((Cb * (∫ t in Ioi (0 : ℝ), wl2_Fe d t) / 2) * (1 / ((d : ℝ) / 2)) *
        (((M : ℝ) ^ ((d : ℝ) / 2))⁻¹)) := by
  set Ke : ℝ := ∫ t in Ioi (0 : ℝ), wl2_Fe d t with hKe
  have hKe0 : 0 ≤ Ke := setIntegral_nonneg measurableSet_Ioi fun t ht => wl2_Fe_nonneg d ht
  have hα : (1 : ℝ) ≤ (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set b : ℕ → ℝ := fun j =>
    (Cb * Ke / 2) * (((((M + 1 + j : ℕ) : ℝ) ^ ((d : ℝ) / 2)) * ((M + 1 + j : ℕ) : ℝ))⁻¹) with hb
  have hb0 : ∀ j, 0 ≤ b j := fun j => by simp only [hb]; positivity
  have hsum : ∀ n, ∑ j ∈ Finset.range n, b j ≤ (Cb * Ke / 2) * (1 / ((d : ℝ) / 2)) * (((M : ℝ) ^ ((d : ℝ) / 2))⁻¹) := by
    intro n
    have := wl2_sum_tail hα hM n
    simp only [hb]
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hbs : Summable b := summable_of_sum_range_le hb0 hsum
  calc ∫⁻ y, ENNReal.ofReal (wl2_qm M x y) ∂μ
      ≤ ∫⁻ y, ∑' j : ℕ, ENNReal.ofReal (wl2_qterm M x y j) ∂μ := lintegral_mono fun y => wl2_ofReal_qm_le M x y
    _ = ∑' j : ℕ, ∫⁻ y, ENNReal.ofReal (wl2_qterm M x y j) ∂μ :=
        lintegral_tsum fun j => (ENNReal.measurable_ofReal.comp (wl2_qterm_measurable_right M x j)).aemeasurable
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (b j) :=
        ENNReal.tsum_le_tsum fun j => wl2_term_lintegral hd hCb x hch (k := M + 1 + j) (by omega)
    _ = ENNReal.ofReal (∑' j, b j) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.tsum_le_of_sum_range_le hb0 hsum)

/-- **`wl_row_qm`.**  `sup_x ∫ q_M(x,y) dμ(y) ≤ C M^{-d/2}` for `M ≥ 1`. -/
theorem wl_row_qm (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ (M : ℕ), 1 ≤ M → ∀ x : Euc d,
      Integrable (fun y => wl2_qm M x y) (HRS.Whole.withDensityReal ρ) ∧
        ∫ y, wl2_qm M x y ∂(HRS.Whole.withDensityReal ρ) ≤ C * (M : ℝ) ^ (-((d : ℝ) / 2)) := by
  obtain ⟨Cb, hCb0, hCb⟩ := wl_chordal_level hd A
  have hKe0 : 0 ≤ ∫ t in Ioi (0 : ℝ), wl2_Fe d t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => wl2_Fe_nonneg d ht
  have hα : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨(Cb * (∫ t in Ioi (0 : ℝ), wl2_Fe d t) / 2) * (1 / ((d : ℝ) / 2)), by positivity,
    fun ρ hρ hA M hM x => ?_⟩
  haveI := wl2_isProb hρ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hrp : (M : ℝ) ^ (-((d : ℝ) / 2)) = (((M : ℝ) ^ ((d : ℝ) / 2))⁻¹) := Real.rpow_neg hM0.le _
  rw [hrp]
  exact wl2_integrable_of_lintegral_le (wl2_qm_measurable_right M x).aemeasurable
    (wl2_qm_nonneg M x) (by positivity)
    (wl2_qm_lintegral hd hCb0 x (fun δ hδ => hCb ρ hρ hA x δ hδ) hM)


/-! ### The Schur-type bound -/

/-- A density `ρ dx` does not charge a point (copy of `wr3_ae_ne`). -/
lemma wl2_ae_ne (hd : 1 ≤ d) (ρ : Euc d → ℝ) (x : Euc d) :
    ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), y ≠ x := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) x
  exact (withDensity_absolutelyContinuous _ _).ae_le h

lemma wl2_B_nonneg (hd : 1 ≤ d) {B : ℝ} {h : Euc d → Euc d → ℝ}
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) : 0 ≤ B := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : Euc d)
  have h1 := hB 0 v hv.symm
  have h2 := HRS.MS.Comm.comm_log_nonneg (0 : Euc d) v
  by_contra hneg
  push Not at hneg
  nlinarith [abs_nonneg (h 0 v)]

/-- **`wl_schur`.**  A symmetric-or-not measurable kernel with `|h| ≤ B (1+K)` off the diagonal has
uniformly bounded `L¹` and `L²` rows and is integrable on `μ ⊗ μ`.  `B ≥ 0` is derived. -/
theorem wl_schur (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ (B : ℝ) (h : Euc d → Euc d → ℝ),
      Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      0 ≤ B ∧
      (∀ x : Euc d,
        Integrable (h x) (HRS.Whole.withDensityReal ρ) ∧
        Integrable (fun y => |h x y| ^ 2) (HRS.Whole.withDensityReal ρ) ∧
        ∫ y, |h x y| ∂(HRS.Whole.withDensityReal ρ) ≤ C * B ∧
        ∫ y, |h x y| ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ C * B ^ 2) ∧
      Integrable (fun p : Euc d × Euc d => h p.1 p.2)
        ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨C1, hC10, hC1⟩ := wl_row_pow hd A 1
  obtain ⟨C2, hC20, hC2⟩ := wl_row_pow hd A 2
  refine ⟨max (1 + C1) (2 + 2 * C2), by positivity, fun ρ hρ hA B h hmeas hbd => ?_⟩
  haveI := wl2_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hB0 : 0 ≤ B := wl2_B_nonneg (by omega) hbd
  refine ⟨hB0, fun x => ?_, ?_⟩
  · have hae : ∀ᵐ y ∂μ, |h x y| ≤ B * (1 + sphericalLogKernel x y) := by
      filter_upwards [wl2_ae_ne (by omega) ρ x] with y hy using hbd x y hy.symm
    have hhm : Measurable (h x) := Measurable.of_uncurry_left (f := h) hmeas
    have hK1 : Integrable (fun y => sphericalLogKernel x y) μ := by
      simpa only [pow_one] using (hC1 ρ hρ hA x).1
    have hK1b : ∫ y, sphericalLogKernel x y ∂μ ≤ C1 := by
      simpa only [pow_one] using (hC1 ρ hρ hA x).2
    have hK2 : Integrable (fun y => sphericalLogKernel x y ^ 2) μ := (hC2 ρ hρ hA x).1
    have hK2b : ∫ y, sphericalLogKernel x y ^ 2 ∂μ ≤ C2 := (hC2 ρ hρ hA x).2
    have hdom1 : Integrable (fun y => B * (1 + sphericalLogKernel x y)) μ :=
      ((integrable_const (1 : ℝ)).add hK1).const_mul B
    have hIh : Integrable (h x) μ :=
      hdom1.mono' hhm.aestronglyMeasurable (by
        filter_upwards [hae] with y hy
        simpa [Real.norm_eq_abs] using hy)
    have hI1 : Integrable (fun y => |h x y|) μ := hIh.abs
    have hdom2 : Integrable (fun y => B ^ 2 * (2 + 2 * sphericalLogKernel x y ^ 2)) μ :=
      ((integrable_const (2 : ℝ)).add (hK2.const_mul 2)).const_mul (B ^ 2)
    have hpt2 : ∀ᵐ y ∂μ, |h x y| ^ 2 ≤ B ^ 2 * (2 + 2 * sphericalLogKernel x y ^ 2) := by
      filter_upwards [hae] with y hy
      have hK := HRS.MS.Comm.comm_log_nonneg x y
      have h1 : |h x y| ^ 2 ≤ (B * (1 + sphericalLogKernel x y)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hy 2
      calc |h x y| ^ 2 ≤ (B * (1 + sphericalLogKernel x y)) ^ 2 := h1
        _ = B ^ 2 * (1 + sphericalLogKernel x y) ^ 2 := by ring
        _ ≤ B ^ 2 * (2 + 2 * sphericalLogKernel x y ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_nonneg (sphericalLogKernel x y - 1)]
    have hI2 : Integrable (fun y => |h x y| ^ 2) μ :=
      hdom2.mono' (hhm.abs.pow_const 2).aestronglyMeasurable (by
        filter_upwards [hpt2] with y hy
        simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg |h x y|)] using hy)
    have hint1 : ∫ y, B * (1 + sphericalLogKernel x y) ∂μ = B * (1 + ∫ y, sphericalLogKernel x y ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const _) hK1]
      simp
    have hint2 : ∫ y, B ^ 2 * (2 + 2 * sphericalLogKernel x y ^ 2) ∂μ =
        B ^ 2 * (2 + 2 * ∫ y, sphericalLogKernel x y ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hK2.const_mul 2), integral_const_mul]
      simp
    refine ⟨hIh, hI2, ?_, ?_⟩
    · calc ∫ y, |h x y| ∂μ ≤ ∫ y, B * (1 + sphericalLogKernel x y) ∂μ := integral_mono_ae hI1 hdom1 hae
        _ = B * (1 + ∫ y, sphericalLogKernel x y ∂μ) := hint1
        _ ≤ B * (1 + C1) := mul_le_mul_of_nonneg_left (by linarith) hB0
        _ ≤ B * max (1 + C1) (2 + 2 * C2) := mul_le_mul_of_nonneg_left (le_max_left _ _) hB0
        _ = _ := mul_comm _ _
    · calc ∫ y, |h x y| ^ 2 ∂μ ≤ ∫ y, B ^ 2 * (2 + 2 * sphericalLogKernel x y ^ 2) ∂μ :=
          integral_mono_ae hI2 hdom2 hpt2
        _ = B ^ 2 * (2 + 2 * ∫ y, sphericalLogKernel x y ^ 2 ∂μ) := hint2
        _ ≤ B ^ 2 * (2 + 2 * C2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ B ^ 2 * max (1 + C1) (2 + 2 * C2) := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
        _ = _ := mul_comm _ _
  · -- integrability on the product
    have hKprod : Integrable (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) (μ.prod μ) := by
      refine (wl2_integrable_of_lintegral_le wl2_K_measurable.aemeasurable
        (fun p => HRS.MS.Comm.comm_log_nonneg p.1 p.2) hC10 ?_).1
      have hm : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (sphericalLogKernel p.1 p.2) :=
        ENNReal.measurable_ofReal.comp wl2_K_measurable
      rw [lintegral_prod _ hm.aemeasurable]
      calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (sphericalLogKernel x y) ∂μ ∂μ
          ≤ ∫⁻ x, ENNReal.ofReal C1 ∂μ := by
            refine lintegral_mono fun x => ?_
            have hK1 : Integrable (fun y => sphericalLogKernel x y) μ := by
              simpa only [pow_one] using (hC1 ρ hρ hA x).1
            have hK1b : ∫ y, sphericalLogKernel x y ∂μ ≤ C1 := by
              simpa only [pow_one] using (hC1 ρ hρ hA x).2
            rw [← ofReal_integral_eq_lintegral_ofReal hK1
              (Filter.Eventually.of_forall fun y => HRS.MS.Comm.comm_log_nonneg x y)]
            exact ENNReal.ofReal_le_ofReal hK1b
        _ = ENNReal.ofReal C1 := by simp
    have hΦ : Integrable (fun p : Euc d × Euc d => B * (1 + sphericalLogKernel p.1 p.2)) (μ.prod μ) :=
      ((integrable_const (1 : ℝ)).add hKprod).const_mul B
    have hset : MeasurableSet {z : Euc d × Euc d | z.1 ≠ z.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    have hae : ∀ᵐ z ∂(μ.prod μ), z.1 ≠ z.2 := by
      rw [Measure.ae_prod_iff_ae_ae hset]
      refine Filter.Eventually.of_forall fun x => ?_
      filter_upwards [wl2_ae_ne (by omega) ρ x] with y hy using hy.symm
    refine hΦ.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with z hz
    simpa [Real.norm_eq_abs] using hbd z.1 z.2 hz

end HRS.MS.Wl
