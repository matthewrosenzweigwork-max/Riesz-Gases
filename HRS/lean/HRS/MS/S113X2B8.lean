import HRS.MS.S113X2B7

/-! # S11.3 X2 part B, B8: the power chain inequality for C^1 exponents (STUB, to be filled) -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.S113X2B

/-- Constant-on-`K` indicator is integrable. -/
theorem s113b_int_ind {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) (D : ℝ) :
    Integrable (K.indicator fun _ : s113b_E n => D) :=
  (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet

/-- Bound for an integral dominated by a `K`-indicator. -/
theorem s113b_int_bd {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) {f : s113b_E n → ℝ} {D : ℝ}
    (h : ∀ x, ‖f x‖ ≤ K.indicator (fun _ => D) x) : ‖∫ x, f x‖ ≤ D * (volume K).toReal := by
  refine (norm_integral_le_of_norm_le (s113b_int_ind hK D) (ae_of_all _ h)).trans ?_
  rw [integral_indicator_const _ hK.measurableSet]
  simp [mul_comm, Measure.real]

/-- Dominated convergence (`ε → 0+`) for `K`-supported bounded integrands. -/
theorem s113b_dct_K {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) {F : ℝ → s113b_E n → ℝ}
    {f : s113b_E n → ℝ} {D : ℝ}
    (hm : ∀ᶠ ε in nhdsWithin (0:ℝ) (Ioi 0), AEStronglyMeasurable (F ε) volume)
    (hb : ∀ᶠ ε in nhdsWithin (0:ℝ) (Ioi 0), ∀ x, ‖F ε x‖ ≤ K.indicator (fun _ => D) x)
    (hl : ∀ x, Tendsto (fun ε => F ε x) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (f x))) :
    Tendsto (fun ε => ∫ x, F ε x) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (∫ x, f x)) :=
  tendsto_integral_filter_of_dominated_convergence _ hm (hb.mono fun _ h => ae_of_all _ h)
    (s113b_int_ind hK D) (ae_of_all _ hl)

theorem s113b_meas_Phi {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable (fun a => s113b_Phi (f a) (g a) (h a)) := by
  unfold s113b_Phi; fun_prop

theorem s113b_meas_Theta {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable (fun a => s113b_Theta (f a) (g a) (h a)) := by
  unfold s113b_Theta s113b_Phi1 s113b_Phi; fun_prop

theorem s113b_meas_PhiP {α : Type*} [MeasurableSpace α] {f g h : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h) : Measurable (fun a => s113b_PhiP (f a) (g a) (h a)) := by
  unfold s113b_PhiP; fun_prop

/-- The source numerator is a continuous function of `(τ, x)`: `R = N / q`. -/
theorem s113b_Rnum {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ}
    (hb : ContDiff ℝ 2 b) (hq : ContDiff ℝ 2 (fun z : ℝ × s113b_E n => q z.1 z.2)) :
    ∃ N : ℝ × s113b_E n → ℝ, Continuous N ∧ ∀ τ x, s113b_R ν b q τ x = N (τ, x) / q τ x := by
  set Q : ℝ × s113b_E n → ℝ := fun z => q z.1 z.2 with hQdef
  have hQd : Differentiable ℝ Q := hq.differentiable (by norm_num)
  set Q1 : ℝ × s113b_E n → s113b_E n →L[ℝ] ℝ :=
    fun z => (fderiv ℝ Q z).comp (ContinuousLinearMap.inr ℝ ℝ (s113b_E n)) with hQ1
  have hQ1c : ContDiff ℝ 1 Q1 := (hq.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hsl : ∀ τ x, HasFDerivAt (q τ) (Q1 (τ, x)) x := fun τ x =>
    (hQd (τ, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right τ x)
  have hsl1 : ∀ τ x, HasFDerivAt (fun y => Q1 (τ, y))
      ((fderiv ℝ Q1 (τ, x)).comp (ContinuousLinearMap.inr ℝ ℝ (s113b_E n))) x := fun τ x =>
    ((hQ1c.differentiable one_ne_zero) (τ, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right τ x)
  have hbk : ∀ k : Fin n, ContDiff ℝ 2 (fun y : s113b_E n => b y k) := fun k =>
    (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hb
  have hc1 : Continuous (fderiv ℝ Q1) := hQ1c.continuous_fderiv (by norm_num)
  have hc0 : Continuous (fderiv ℝ Q) := hq.continuous_fderiv (by norm_num)
  have hcQ1 : Continuous Q1 := hQ1c.continuous
  have hDk : ∀ k : Fin n, Continuous (fun y : s113b_E n =>
      fderiv ℝ (fun y => b y k) y (EuclideanSpace.single k 1)) := fun k =>
    ((hbk k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbc : ∀ k : Fin n, Continuous (fun y : s113b_E n => b y k) := fun k => (hbk k).continuous
  have hQc : Continuous Q := hq.continuous
  refine ⟨fun z => ν * (∑ k : Fin n, fderiv ℝ Q1 z (0, EuclideanSpace.single k 1) (EuclideanSpace.single k 1))
    - ∑ k : Fin n, (Q z * fderiv ℝ (fun y => b y k) z.2 (EuclideanSpace.single k 1) +
        b z.2 k * Q1 z (EuclideanSpace.single k 1)) - fderiv ℝ Q z (1, 0), ?_, fun τ x => ?_⟩
  · have h1 : ∀ k : Fin n, Continuous (fun z : ℝ × s113b_E n =>
        fderiv ℝ (fun y => b y k) z.2 (EuclideanSpace.single k 1)) := fun k => (hDk k).comp continuous_snd
    have h2 : ∀ k : Fin n, Continuous (fun z : ℝ × s113b_E n => b z.2 k) := fun k => (hbc k).comp continuous_snd
    fun_prop
  · have h1 : s113b_lap (q τ) x = ∑ k : Fin n, fderiv ℝ Q1 (τ, x) (0, EuclideanSpace.single k 1)
        (EuclideanSpace.single k 1) := by
      have : fderiv ℝ (q τ) = fun y => Q1 (τ, y) := funext fun y => (hsl τ y).fderiv
      simp only [s113b_lap, this, (hsl1 τ x).fderiv]; simp
    have h2 : s113b_div (fun y => q τ y • b y) x = ∑ k : Fin n, (Q (τ, x) *
        fderiv ℝ (fun y => b y k) x (EuclideanSpace.single k 1) +
        b x k * Q1 (τ, x) (EuclideanSpace.single k 1)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hh : HasFDerivAt (fun y => q τ y * b y k) (q τ x • fderiv ℝ (fun y => b y k) x + b x k • Q1 (τ, x)) x :=
        (hsl τ x).mul ((hbk k).differentiable (by norm_num) x).hasFDerivAt
      have : (fun y => (q τ y • b y) k) = fun y => q τ y * b y k := by ext y; simp
      rw [this, hh.fderiv]; simp [hQdef]
    have h3 : deriv (fun σ => q σ x) τ = fderiv ℝ Q (τ, x) (1, 0) := by
      have := ((hQd (τ, x)).hasFDerivAt.comp τ (hasFDerivAt_prodMk_left τ x)).hasDerivAt.deriv
      show deriv (Q ∘ fun e => (e, x)) τ = _
      simpa using this
    simp only [s113b_R, h1, h2, h3]

theorem s113b_chain_C1 {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    s113b_M q u p t - s113b_M q u p s ≤ ∫ τ in s..t, s113b_Gp ν b q u p τ := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hK := hD.hKc
  have hpc : Continuous p := hp.continuous
  have hp'c : Continuous (deriv p) := hp.continuous_deriv le_rfl
  obtain ⟨p1, hp1', hp1b⟩ := isCompact_Icc.exists_forall_le' (a := (1:ℝ)) hpc.continuousOn hp1
  obtain ⟨p2, hp2⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hpc.continuousOn
  obtain ⟨Cd, hCd⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hp'c.continuousOn
  have hQc : Continuous (fun z : ℝ × s113b_E n => q z.1 z.2) := hD.hq.continuous
  have hS : IsCompact (Icc (0:ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨m, hm0, hm⟩ := hS.exists_forall_le' (a := (0:ℝ)) hQc.continuousOn
    (fun z hz => hD.hq0 z.1 hz.1 z.2)
  obtain ⟨Cq, hqC, hq1⟩ : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ τ ∈ Icc (0:ℝ) T, ∀ x ∈ K, |q τ x| ≤ Cq := by
    obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn hQc.continuousOn
    exact ⟨max c 0, le_max_right _ _, fun τ hτ x hx => (hc (τ, x) ⟨hτ, hx⟩).trans (le_max_left _ _)⟩
  obtain ⟨N, hNc, hRN⟩ := s113b_Rnum (ν := ν) hD.hb hD.hq
  obtain ⟨Cn, hnC, hn1⟩ : ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ τ ∈ Icc (0:ℝ) T, ∀ x ∈ K, |N (τ, x)| ≤ Cn := by
    obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn hNc.continuousOn
    exact ⟨max c 0, le_max_right _ _, fun τ hτ x hx => (hc (τ, x) ⟨hτ, hx⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC⟩ := s113b_uniform_bound p1 p2 (B / m) hp1'
  have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Ioi 0), ε ∈ Ioc (0:ℝ) 1 := Ioc_mem_nhdsGT one_pos
  have hqm : Measurable (fun z : ℝ × s113b_E n => q z.1 z.2) := hQc.measurable
  have hrm : Measurable (fun z : ℝ × s113b_E n => u z.1 z.2 / q z.1 z.2) := hD.hum.div hqm
  have hpm : Measurable (fun z : ℝ × s113b_E n => p z.1) := hpc.measurable.comp measurable_fst
  have hdm : Measurable (fun z : ℝ × s113b_E n => deriv p z.1) := hp'c.measurable.comp measurable_fst
  have hRm : Measurable (fun z : ℝ × s113b_E n => s113b_R ν b q z.1 z.2) := by
    have : (fun z : ℝ × s113b_E n => s113b_R ν b q z.1 z.2) = fun z => N z / q z.1 z.2 :=
      funext fun z => hRN z.1 z.2
    rw [this]; exact hNc.measurable.div hqm
  have hB0 : 0 ≤ B := (hD.hu0 0 0).trans (hD.huB 0 ⟨le_rfl, hT⟩ 0)
  have hrz : ∀ τ x, x ∉ K → u τ x / q τ x = 0 := fun τ x hx => by simp [hD.hKu τ x hx]
  have hrb : ∀ τ ∈ Icc (0:ℝ) T, ∀ x, 0 ≤ u τ x / q τ x ∧ u τ x / q τ x ≤ B / m := fun τ hτ x =>
    ⟨div_nonneg (hD.hu0 τ x) (hD.hq0 τ hτ x).le, by
      by_cases hx : x ∈ K
      · exact div_le_div₀ hB0 (hD.huB τ hτ x) hm0 (hm (τ, x) ⟨hτ, hx⟩)
      · rw [hrz τ x hx]; positivity⟩
  have hpr : ∀ τ ∈ Icc (0:ℝ) T, p τ ∈ Icc p1 p2 := fun τ hτ =>
    ⟨hp1b τ hτ, (le_abs_self _).trans (hp2 τ hτ)⟩
  have hU : ∀ τ ∈ Icc (0:ℝ) T, ∀ ε ∈ Ioc (0:ℝ) 1, ∀ x,
      |s113b_Phi (p τ) ε (u τ x / q τ x)| ≤ C ∧ |s113b_Theta (p τ) ε (u τ x / q τ x)| ≤ C ∧
        |s113b_PhiP (p τ) ε (u τ x / q τ x)| ≤ C := fun τ hτ ε hε x => by
    have := hC (p τ) (hpr τ hτ) ε hε _ ⟨(hrb τ hτ x).1, (hrb τ hτ x).2⟩
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hU 0 ⟨le_rfl, hT⟩ 1 ⟨one_pos, le_rfl⟩ 0).1
  have hL : ∀ τ ∈ Icc (0:ℝ) T, ∀ x, |(u τ x / q τ x) ^ p τ| ≤ C ∧
      |(u τ x / q τ x) ^ p τ * Real.log (u τ x / q τ x)| ≤ C := fun τ hτ x =>
    ⟨le_of_tendsto (s113b_tendsto_Phi (hp1 τ hτ) _ (hrb τ hτ x).1).abs
      (hev.mono fun ε hε => (hU τ hτ ε hε x).1),
     le_of_tendsto (s113b_tendsto_PhiP (hp1 τ hτ) _ (hrb τ hτ x).1).abs
      (hev.mono fun ε hε => (hU τ hτ ε hε x).2.2)⟩
  have hdC : 0 ≤ Cd := (norm_nonneg _).trans (hCd 0 ⟨le_rfl, hT⟩)
  have hRq : ∀ τ ∈ Icc (0:ℝ) T, ∀ x, q τ x * s113b_R ν b q τ x = N (τ, x) := fun τ hτ x => by
    rw [hRN]; field_simp [(hD.hq0 τ hτ x).ne']
  have kF : ∀ τ ∈ Icc (0:ℝ) T, ∀ ε ∈ Ioc (0:ℝ) 1, ∀ x,
      ‖s113b_F q p ε τ x (u τ x)‖ ≤ K.indicator (fun _ => Cq * C) x := by
    intro τ hτ ε hε x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, s113b_F, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hq1 τ hτ x hx) (hU τ hτ ε hε x).1 (abs_nonneg _) hqC
    · rw [indicator_of_notMem hx]; simp [s113b_F, hrz τ x hx, s113b_Phi_zero]
  have kR : ∀ τ ∈ Icc (0:ℝ) T, ∀ ε ∈ Ioc (0:ℝ) 1, ∀ x,
      ‖q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (u τ x / q τ x) +
        deriv p τ * q τ x * s113b_PhiP (p τ) ε (u τ x / q τ x)‖ ≤
        K.indicator (fun _ => Cn * C + Cd * Cq * C) x := by
    intro τ hτ ε hε x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, hRq τ hτ x]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul (hn1 τ hτ x hx) (hU τ hτ ε hε x).2.1 (abs_nonneg _) hnC
      · rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (by simpa using hCd τ hτ) (hq1 τ hτ x hx) (abs_nonneg _) hdC)
          (hU τ hτ ε hε x).2.2 (abs_nonneg _) (mul_nonneg hdC hqC)
    · rw [indicator_of_notMem hx]; simp [hrz τ x hx, s113b_Theta_zero, s113b_PhiP]
  have kA : ∀ τ ∈ Icc (0:ℝ) T, ∀ x,
      ‖q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ p τ‖ ≤ K.indicator (fun _ => Cn * C) x := by
    intro τ hτ x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, hRq τ hτ x, abs_mul]
      exact mul_le_mul (hn1 τ hτ x hx) (hL τ hτ x).1 (abs_nonneg _) hnC
    · rw [indicator_of_notMem hx]
      simp [hrz τ x hx, Real.zero_rpow (by linarith [hp1 τ hτ] : p τ ≠ 0)]
  have kB : ∀ τ ∈ Icc (0:ℝ) T, ∀ x,
      ‖q τ x * (u τ x / q τ x) ^ p τ * Real.log (u τ x / q τ x)‖ ≤ K.indicator (fun _ => Cq * C) x := by
    intro τ hτ x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Real.norm_eq_abs, mul_assoc, abs_mul]
      exact mul_le_mul (hq1 τ hτ x hx) (hL τ hτ x).2 (abs_nonneg _) hqC
    · rw [indicator_of_notMem hx]; simp [hrz τ x hx]
  have hA : ∀ τ ∈ Icc (0:ℝ) T, Tendsto (fun ε => ∫ x, s113b_F q p ε τ x (u τ x))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (s113b_M q u p τ)) := by
    intro τ hτ
    have hm' : ∀ ε, Measurable (fun x => s113b_F q p ε τ x (u τ x)) := fun ε =>
      (hqm.mul (s113b_meas_Phi hpm (measurable_const (a := ε)) hrm)).comp measurable_prodMk_left
    exact s113b_dct_K (f := fun x => q τ x * (u τ x / q τ x) ^ p τ) hK (D := Cq * C)
      (Eventually.of_forall fun ε => (hm' ε).aestronglyMeasurable)
      (hev.mono fun ε hε => kF τ hτ ε hε)
      fun x => (s113b_tendsto_Phi (hp1 τ hτ) _ (hrb τ hτ x).1).const_mul (q τ x)
  have hB : ∀ τ ∈ Icc (0:ℝ) T, Tendsto (fun ε => s113b_rhsE ν b q p ε τ (fun x => u τ x / q τ x))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (s113b_Gp ν b q u p τ)) := by
    intro τ hτ
    have hmA : Measurable (fun x => q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ p τ) :=
      ((hqm.mul hRm).mul (hrm.pow hpm)).comp measurable_prodMk_left
    have hmB : Measurable (fun x => q τ x * (u τ x / q τ x) ^ p τ * Real.log (u τ x / q τ x)) :=
      ((hqm.mul (hrm.pow hpm)).mul (Real.measurable_log.comp hrm)).comp measurable_prodMk_left
    have hiA := Integrable.mono' (s113b_int_ind hK (Cn * C)) hmA.aestronglyMeasurable
      (ae_of_all _ (kA τ hτ))
    have hiB := Integrable.mono' (s113b_int_ind hK (Cq * C)) hmB.aestronglyMeasurable
      (ae_of_all _ (kB τ hτ))
    have hG : ∫ x, ((p τ - 1) * (q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ p τ) +
        deriv p τ * (q τ x * (u τ x / q τ x) ^ p τ * Real.log (u τ x / q τ x))) =
        s113b_Gp ν b q u p τ := by
      rw [integral_add (hiA.const_mul _) (hiB.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      unfold s113b_Gp; rfl
    have hm' : ∀ ε, Measurable (fun x => q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (u τ x / q τ x) +
        deriv p τ * q τ x * s113b_PhiP (p τ) ε (u τ x / q τ x)) := fun ε =>
      (((hqm.mul hRm).mul (s113b_meas_Theta hpm (measurable_const (a := ε)) hrm)).add
        ((hdm.mul hqm).mul (s113b_meas_PhiP hpm (measurable_const (a := ε)) hrm))).comp measurable_prodMk_left
    rw [← hG]
    refine s113b_dct_K hK (D := Cn * C + Cd * Cq * C)
      (Eventually.of_forall fun ε => (hm' ε).aestronglyMeasurable)
      (hev.mono fun ε hε => kR τ hτ ε hε) fun x => ?_
    have := ((s113b_tendsto_Theta (hp1 τ hτ) _ (hrb τ hτ x).1).const_mul (q τ x * s113b_R ν b q τ x)).add
      ((s113b_tendsto_PhiP (hp1 τ hτ) _ (hrb τ hτ x).1).const_mul (deriv p τ * q τ x))
    convert this using 2; ring
  have hmem : ∀ τ ∈ uIoc s t, τ ∈ Icc (0:ℝ) T := fun τ h => by
    rw [uIoc_of_le hst] at h; exact ⟨hs.trans h.1.le, h.2.trans htT⟩
  have hC' : Tendsto (fun ε => ∫ τ in s..t, s113b_rhsE ν b q p ε τ (fun x => u τ x / q τ x))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (∫ τ in s..t, s113b_Gp ν b q u p τ)) := by
    have hmJ : ∀ ε, Measurable (fun z : ℝ × s113b_E n =>
        q z.1 z.2 * s113b_R ν b q z.1 z.2 * s113b_Theta (p z.1) ε (u z.1 z.2 / q z.1 z.2) +
        deriv p z.1 * q z.1 z.2 * s113b_PhiP (p z.1) ε (u z.1 z.2 / q z.1 z.2)) := fun ε =>
      ((hqm.mul hRm).mul (s113b_meas_Theta hpm measurable_const hrm)).add
        ((hdm.mul hqm).mul (s113b_meas_PhiP hpm measurable_const hrm))
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (Cn * C + Cd * Cq * C) * (volume K).toReal)
      (Eventually.of_forall fun ε => ?_) (hev.mono fun ε hε => ae_of_all _ fun τ hτ' => ?_)
      intervalIntegrable_const (ae_of_all _ fun τ hτ' => hB τ (hmem τ hτ'))
    · exact ((hmJ ε).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact s113b_int_bd hK (kR τ (hmem τ hτ') ε hε)
  have ht : t ∈ Icc (0:ℝ) T := ⟨hs.trans hst, htT⟩
  have hs' : s ∈ Icc (0:ℝ) T := ⟨hs, hst.trans htT⟩
  refine le_of_tendsto_of_tendsto ((hA t ht).sub (hA s hs')) hC' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact s113b_eps_chain hD hp hp1 hε hs hst htT

end HRS.MS.S113X2B
