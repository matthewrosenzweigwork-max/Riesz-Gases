import HRS.Energy.Commutator.SmearAuxD

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2), part E: the limit `l → 0` of the slice profiles

`κ_d = 1/|S^{d-1}|`, the Newton profile ODE, and the asymptotics of the Yukawa profile as `l → 0⁺`
needed for the Coulomb slice: `A_l(η) = l ∫_0^η r^{d-1} Γ_l → 0` (`Aint_tendsto`), the sandwich
`0 ≤ (N(r) - N(η)) - (Γ_l(r) - Γ_l(η)) ≤ A_l(η) ∫_r^η s^{1-d}` (`f_sandwich`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators Pointwise
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

/-- `κ_d = 1/|S^{d-1}| = Γ(d/2)/(2π^{d/2})` -/
def kappa (d : ℕ) : ℝ := Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2))

theorem kappa_pos (d : ℕ) (hd : 1 ≤ d) : 0 < kappa d := by
  unfold kappa
  have h0 : (0:ℝ) < (d : ℝ) / 2 := by
    have : (0:ℝ) < d := by exact_mod_cast hd
    positivity
  have := Real.Gamma_pos_of_pos h0
  positivity

/-- `A_l(ρ) = l ∫_0^ρ s^{d-1} Γ_l(s) ds`. -/
def Aint (d : ℕ) (l ρ : ℝ) : ℝ := l * ∫ s in Ioc (0 : ℝ) ρ, s ^ (d - 1) * yukawa d l s

theorem Aint_nonneg (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (ρ : ℝ) : 0 ≤ Aint d l ρ := by
  unfold Aint
  refine mul_nonneg hl.le (setIntegral_nonneg measurableSet_Ioc fun s hs => ?_)
  exact mul_nonneg (pow_nonneg hs.1.le _) ((yukawa_ode hd hl).1 s hs.1).le

theorem Aint_mono (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (h : ρ ≤ η) :
    Aint d l ρ ≤ Aint d l η := by
  unfold Aint
  refine mul_le_mul_of_nonneg_left ?_ hl.le
  refine setIntegral_mono_set (int_flux hd hl hη).1 ?_ (Eventually.of_forall (Ioc_subset_Ioc_right h))
  exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs =>
    mul_nonneg (pow_nonneg hs.1.le _) ((yukawa_ode hd hl).1 s hs.1).le)

theorem qq_eq (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {ρ : ℝ} (hρ : 0 < ρ) :
    -(ρ ^ (d - 1) * deriv (yukawa d l) ρ) = kappa d - Aint d l ρ := by
  obtain ⟨-, h⟩ := int_flux hd hl hρ
  unfold Aint kappa
  linarith


theorem neg_deriv_yukawa_eq (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {s : ℝ} (hs : 0 < s) :
    -deriv (yukawa d l) s = (kappa d - Aint d l s) / s ^ (d - 1) := by
  have := qq_eq hd hl hs
  have hp : s ^ (d - 1) ≠ 0 := pow_ne_zero _ hs.ne'
  field_simp
  linarith

theorem continuousAt_deriv_yukawa (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (deriv (yukawa d l)) s :=
  cont_of_q (fun r hr => hasDerivAt_flux hd hl hr) s hs

/-- the radial heat mass `m(s) = ∫_0^η r^{d-1} g_s(r) dr`. -/
def mrad (d : ℕ) (η s : ℝ) : ℝ := ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * SliceAux.gprof d s r

theorem mrad_nonneg (η : ℝ) {s : ℝ} (hs : 0 < s) : 0 ≤ mrad d η s :=
  setIntegral_nonneg measurableSet_Ioc fun r hr =>
    mul_nonneg (pow_nonneg hr.1.le _) (SliceAux.gprof_pos d hs r).le

theorem mrad_le_one (hd : 1 ≤ d) {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    (d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1) * mrad d η s ≤ 1 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hint : Integrable (fun x : Euc d => SliceAux.gprof d s ‖x‖) := by
    have := integrable_gφ hd hs (0 : Euc d)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp [gφ_eq]
  have h1 : ∫ x : Euc d, SliceAux.gprof d s ‖x‖ = 1 := by
    have := integral_gφ hd hs (0 : Euc d)
    simpa [gφ_eq] using this
  have h2 := integral_fun_norm_addHaar (volume : Measure (Euc d)) (fun r => SliceAux.gprof d s r)
  rw [h1, hfr] at h2
  have h3 := (integrable_fun_norm_addHaar (volume : Measure (Euc d)) (f := fun r => SliceAux.gprof d s r)).1 hint
  rw [hfr] at h3
  have hle : mrad d η s ≤ ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • SliceAux.gprof d s r := by
    unfold mrad
    simp only [smul_eq_mul]
    refine setIntegral_mono_set (by simpa using h3) ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr =>
      mul_nonneg (pow_nonneg (le_of_lt hr) _) (SliceAux.gprof_pos d hs r).le)
  have hω : 0 ≤ (d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1) := by positivity
  calc (d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1) * mrad d η s
      ≤ (d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1) * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) • SliceAux.gprof d s r :=
        mul_le_mul_of_nonneg_left hle hω
    _ = 1 := by
        rw [nsmul_eq_mul, smul_eq_mul] at h2
        linarith

theorem mrad_le_decay (hd : 1 ≤ d) {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    mrad d η s ≤ (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * (η ^ d / d) := by
  unfold mrad
  have hc : 0 < (4 * Real.pi * s) ^ (-(d : ℝ) / 2) := by positivity
  have h1 : ∀ r ∈ Ioc (0 : ℝ) η, r ^ (d - 1) * SliceAux.gprof d s r ≤
      (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * r ^ (d - 1) := by
    intro r hr
    unfold SliceAux.gprof
    have : Real.exp (-r ^ 2 / (4 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ r ^ 2 / (4 * s) := by positivity
      rw [neg_div]; linarith
    have hp := pow_nonneg hr.1.le (d - 1)
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hc.le hp)]
  have hI : IntegrableOn (fun r : ℝ => (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * r ^ (d - 1)) (Ioc 0 η) :=
    (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
  have hI2 : IntegrableOn (fun r : ℝ => r ^ (d - 1) * SliceAux.gprof d s r) (Ioc 0 η) := by
    refine Integrable.mono' hI ?_ ?_
    · exact (by unfold SliceAux.gprof; fun_prop : Continuous fun r : ℝ => r ^ (d - 1) * SliceAux.gprof d s r).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr.1.le _) (SliceAux.gprof_pos d hs r).le)]
      exact h1 r hr
  calc ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * SliceAux.gprof d s r
      ≤ ∫ r in Ioc (0 : ℝ) η, (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * r ^ (d - 1) :=
        setIntegral_mono_on hI2 hI measurableSet_Ioc h1
    _ = (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * (η ^ d / d) := by
        rw [integral_const_mul]
        congr 1
        rw [← intervalIntegral.integral_of_le hη.le, integral_pow]
        have : d - 1 + 1 = d := by omega
        rw [this]
        simp [zero_pow (by omega : d ≠ 0), Nat.cast_sub hd]


theorem Aint_eq (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    Aint d l η = ∫ v in Ioi (0 : ℝ), Real.exp (-v) * mrad d η (v / l) := by
  have hint1 := (int_flux hd hl hη).1
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 ^ (d - 1) * (Real.exp (-l * p.2) * SliceAux.gprof d p.2 p.1)) := by
    unfold SliceAux.gprof; fun_prop
  have hI : Integrable (Function.uncurry fun (r s : ℝ) => r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r))
      (((volume : Measure ℝ).restrict (Ioc 0 η)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
    refine (integrable_prod_iff (show AEStronglyMeasurable (Function.uncurry fun (r s : ℝ) =>
      r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r)) _ from hmeas.aestronglyMeasurable)).2 ?_
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      exact (SliceAux.integrableOn_yk hl hd hr.1).const_mul (r ^ (d - 1))
    · refine hint1.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      have hnn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r) :=
        fun s hs => mul_nonneg (pow_nonneg hr.1.le _) (mul_nonneg (Real.exp_pos _).le (SliceAux.gprof_pos d hs r).le)
      have : ∫ s in Ioi (0 : ℝ), ‖r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r)‖ =
          ∫ s in Ioi (0 : ℝ), r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r) :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hnn s hs)]
      simp only [Function.uncurry_apply_pair]
      rw [this, integral_const_mul]
      rfl
  have hswap := integral_integral_swap hI
  have e1 : ∫ r in Ioc (0 : ℝ) η, ∫ s in Ioi (0 : ℝ), r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r) =
      ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * yukawa d l r := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [integral_const_mul]; rfl
  have e2 : ∀ s : ℝ, ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * (Real.exp (-l * s) * SliceAux.gprof d s r) =
      Real.exp (-l * s) * mrad d η s := by
    intro s
    unfold mrad
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun r => by ring)
  rw [e1] at hswap
  simp_rw [e2] at hswap
  unfold Aint
  rw [hswap]
  have := integral_comp_mul_left_Ioi (fun v : ℝ => Real.exp (-v) * mrad d η (v / l)) 0 hl
  simp only [mul_zero] at this
  have e3 : ∀ x : ℝ, Real.exp (-(l * x)) * mrad d η (l * x / l) = Real.exp (-l * x) * mrad d η x := by
    intro x; rw [mul_div_cancel_left₀ _ hl.ne']; congr 2; ring
  simp_rw [e3] at this
  rw [this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]


theorem measurable_mrad (η : ℝ) : Measurable (mrad d η) := by
  unfold mrad
  have hm : Measurable (fun p : ℝ × ℝ => p.2 ^ (d - 1) * SliceAux.gprof d p.1 p.2) := by
    unfold SliceAux.gprof; fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioc 0 η))).measurable

theorem Aint_tendsto (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun l : ℝ => Aint d l η) (𝓝[>] 0) (𝓝 0) := by
  have hω : 0 < (d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1) := by
    have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
    have h1 : (0:ℝ) < d := by exact_mod_cast hd
    have h2 : 0 < (volume : Measure (Euc d)).real (ball 0 1) := by
      rw [real_volume_ball_one hd]
      have := Real.Gamma_pos_of_pos (show (0:ℝ) < (d : ℝ) / 2 + 1 by positivity)
      positivity
    positivity
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), Aint d l η = ∫ v in Ioi (0 : ℝ), Real.exp (-v) * mrad d η (v / l) := by
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact Aint_eq hd hl hη
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (l := 𝓝[>] (0 : ℝ)) (F := fun l v => Real.exp (-v) * mrad d η (v / l)) (f := fun _ => (0:ℝ))
    (bound := fun v => Real.exp (-v) * (1 / ((d : ℝ) * (volume : Measure (Euc d)).real (ball 0 1)))) ?_ ?_ ?_ ?_
  · simpa using this
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact ((by fun_prop : Measurable fun v : ℝ => Real.exp (-v)).mul
      ((measurable_mrad η).comp (measurable_id.div_const l))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with l hl
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv' : 0 < v / l := div_pos hv hl
    have h1 := mrad_nonneg (d := d) η hv'
    have h2 := mrad_le_one hd hη hv'
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h1)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    rw [le_div_iff₀ hω]; linarith
  · have : Integrable (fun v : ℝ => Real.exp (-v)) ((volume : Measure ℝ).restrict (Ioi 0)) := by
      have := integrableOn_exp_mul_Ioi (a := -1) (by norm_num) (0 : ℝ)
      refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
      simp
    exact this.mul_const _
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv => ?_)
    have hv0 : (0:ℝ) < v := hv
    have hlim : Tendsto (fun l : ℝ => (4 * Real.pi * (v / l)) ^ (-((d : ℝ) / 2))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun l : ℝ => 4 * Real.pi * v * l⁻¹) (𝓝[>] 0) atTop :=
        (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (by positivity)
      have h2 := (tendsto_rpow_neg_atTop (y := (d : ℝ) / 2) (by
        have : (0:ℝ) < d := by exact_mod_cast hd
        positivity)).comp h1
      refine h2.congr (fun l => ?_)
      simp only [Function.comp]
      rw [show 4 * Real.pi * v * l⁻¹ = 4 * Real.pi * (v / l) by ring]
    have hlim2 := (hlim.const_mul (η ^ d / d)).const_mul (Real.exp (-v))
    simp only [mul_zero] at hlim2
    refine squeeze_zero' ?_ ?_ hlim2
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact mul_nonneg (Real.exp_pos _).le (mrad_nonneg η (div_pos hv0 hl))
    · filter_upwards [self_mem_nhdsWithin] with l hl
      have := mrad_le_decay hd hη (div_pos hv0 hl)
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      calc mrad d η (v / l) ≤ _ := this
        _ = _ := by rw [neg_div, mul_comm]


theorem yukawa_sub_eq (hd : 1 ≤ d) {l r η : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r ≤ η) :
    yukawa d l r - yukawa d l η = ∫ s in r..η, -deriv (yukawa d l) s := by
  have hpos : ∀ s ∈ Icc r η, 0 < s := fun s hs => lt_of_lt_of_le hr hs.1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := r) (b := η) (f := fun s => -yukawa d l s)
    (f' := fun s => -deriv (yukawa d l) s) (fun s hs => by
      rw [uIcc_of_le hrη] at hs
      exact (hasDerivAt_yukawa hd hl (hpos s hs)).neg) (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hrη]
      exact fun s hs => (continuousAt_deriv_yukawa hd hl (hpos s hs)).neg.continuousWithinAt)
  rw [this]; ring

theorem pow_mul_sub_le (hd : 1 ≤ d) {l r η : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r ≤ η) :
    r ^ d * (yukawa d l r - yukawa d l η) ≤ kappa d * r * (η - r) := by
  have hpos : ∀ s ∈ Icc r η, 0 < s := fun s hs => lt_of_lt_of_le hr hs.1
  rw [yukawa_sub_eq hd hl hr hrη, ← intervalIntegral.integral_const_mul]
  have hc : ∫ s in r..η, kappa d * r = kappa d * r * (η - r) := by
    rw [intervalIntegral.integral_const]; simp [mul_comm]
  rw [← hc]
  refine intervalIntegral.integral_mono_on hrη ?_ ?_ fun s hs => ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hrη]
    exact fun s hs => (continuousAt_deriv_yukawa hd hl (hpos s hs)).neg.continuousWithinAt.const_mul _
  · exact intervalIntegrable_const
  · have hs0 := hpos s hs
    rw [neg_deriv_yukawa_eq hd hl hs0]
    have hA := Aint_nonneg hd hl s
    have hp : r ^ d = r * r ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    have h1 : r ^ (d - 1) ≤ s ^ (d - 1) := pow_le_pow_left₀ hr.le hs.1 _
    have hk := kappa_pos d hd
    rw [hp]
    rw [show r * r ^ (d - 1) * ((kappa d - Aint d l s) / s ^ (d - 1)) = r * (r ^ (d - 1) / s ^ (d - 1)) * (kappa d - Aint d l s) by ring]
    have hq : r ^ (d - 1) / s ^ (d - 1) ≤ 1 := (div_le_one (pow_pos hs0 _)).2 h1
    have hq0 : 0 ≤ r ^ (d - 1) / s ^ (d - 1) := div_nonneg (pow_nonneg hr.le _) (pow_pos hs0 _).le
    nlinarith [mul_nonneg hr.le hq0, mul_le_mul_of_nonneg_left hq hr.le]

theorem int_f_formula (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    IntegrableOn (fun r : ℝ => r * (kappa d - Aint d l r)) (Ioc 0 η) ∧
    ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η) =
      (1 / d) * ∫ r in Ioc (0 : ℝ) η, r * (kappa d - Aint d l r) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hyk := yukawa_ode hd hl
  set Φ : ℝ → ℝ := fun r => r ^ d * (yukawa d l r - yukawa d l η) / d with hΦ
  set Φ' : ℝ → ℝ := fun r => r ^ (d - 1) * (yukawa d l r - yukawa d l η) - r * (kappa d - Aint d l r) / d with hΦ'
  have hderiv : ∀ r, 0 < r → HasDerivAt Φ (Φ' r) r := by
    intro r hr
    have h1 : HasDerivAt (fun r : ℝ => r ^ d) ((d : ℝ) * r ^ (d - 1)) r := hasDerivAt_pow d r
    have h2 : HasDerivAt (fun r : ℝ => yukawa d l r - yukawa d l η) (deriv (yukawa d l) r) r :=
      (hasDerivAt_yukawa hd hl hr).sub_const _
    have h3 := ((h1.mul h2).div_const (d : ℝ))
    refine h3.congr_deriv ?_
    have := qq_eq hd hl hr
    have hp : r ^ d = r * r ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [hΦ']
    have hq : r ^ (d - 1) * deriv (yukawa d l) r = -(kappa d - Aint d l r) := by linarith
    field_simp
    rw [hp]
    nlinarith [hq]
  have hnn : ∀ r, 0 < r → r ≤ η → 0 ≤ yukawa d l r - yukawa d l η := by
    intro r hr hrη
    rcases eq_or_lt_of_le hrη with h | h
    · rw [h]; simp
    · linarith [hyk.2.1 r η hr h]
  have hbd : ∀ r ∈ Icc (0:ℝ) η, 0 ≤ Φ r ∧ Φ r ≤ kappa d * η / d * r := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · subst h0; simp [hΦ, zero_pow (by omega : d ≠ 0)]
    · refine ⟨div_nonneg (mul_nonneg (pow_nonneg hr.1 _) (hnn r hpos hr.2)) hdr.le, ?_⟩
      have h1 := pow_mul_sub_le hd hl hpos hr.2
      simp only [hΦ]
      rw [div_le_iff₀ hdr]
      have hk := kappa_pos d hd
      have h2 : kappa d * r * (η - r) ≤ kappa d * η * r := by nlinarith [mul_pos hk hpos]
      calc r ^ d * (yukawa d l r - yukawa d l η) ≤ kappa d * r * (η - r) := h1
        _ ≤ kappa d * η * r := h2
        _ = kappa d * η / d * r * d := by field_simp
  have hcont : ContinuousOn Φ (Icc 0 η) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · subst h0
      have h00 : Φ 0 = 0 := by simp [hΦ, zero_pow (by omega : d ≠ 0)]
      rw [ContinuousWithinAt, h00]
      refine squeeze_zero' ?_ ?_ ?_ (g := fun r => kappa d * η / d * r)
      · filter_upwards [self_mem_nhdsWithin] with r hr using (hbd r hr).1
      · filter_upwards [self_mem_nhdsWithin] with r hr using (hbd r hr).2
      · exact ((continuous_const.mul continuous_id : Continuous fun r : ℝ => kappa d * η / d * r).tendsto' 0 0
          (by simp)).mono_left nhdsWithin_le_nhds
    · exact (hderiv r hpos).continuousAt.continuousWithinAt
  -- integrability of the derivative
  have hi1 : IntegrableOn (fun r : ℝ => r ^ (d - 1) * (yukawa d l r - yukawa d l η)) (Ioc 0 η) := by
    have h := (int_flux hd hl hη).1
    have h2 : IntegrableOn (fun r : ℝ => yukawa d l η * r ^ (d - 1)) (Ioc 0 η) :=
      (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
    refine (h.sub h2).congr_fun (fun r _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]; ring
  have hi2 : IntegrableOn (fun r : ℝ => r * (kappa d - Aint d l r) / d) (Ioc 0 η) := by
    have hm : Measurable (fun r : ℝ => (r ^ d * -deriv (yukawa d l) r) / d) :=
      ((measurable_id.pow_const d).mul (measurable_deriv _).neg).div_const _
    have hpt : ∀ r ∈ Ioc (0:ℝ) η, r * (kappa d - Aint d l r) / d = (r ^ d * -deriv (yukawa d l) r) / d := by
      intro r hr
      have := qq_eq hd hl hr.1
      have hp : r ^ d = r * r ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
      rw [hp]
      have : kappa d - Aint d l r = -(r ^ (d - 1) * deriv (yukawa d l) r) := by linarith
      rw [this]; ring
    have hae : AEStronglyMeasurable (fun r : ℝ => r * (kappa d - Aint d l r) / d) (volume.restrict (Ioc 0 η)) :=
      hm.aestronglyMeasurable.congr ((ae_restrict_iff' measurableSet_Ioc).2
        (Eventually.of_forall fun r hr => (hpt r hr).symm))
    refine Integrable.mono' (integrable_const (η * kappa d / d)) hae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
    have hq := qq_eq hd hl hr.1
    have hpos : 0 < -(r ^ (d - 1) * deriv (yukawa d l) r) :=
      neg_pos.2 (mul_neg_of_pos_of_neg (pow_pos hr.1 _) (deriv_yukawa_neg hd hl hr.1))
    have hA := Aint_nonneg hd hl r
    have hk := kappa_pos d hd
    have h0 : 0 ≤ kappa d - Aint d l r := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg hr.1.le h0) hdr.le)]
    rw [div_le_div_iff_of_pos_right hdr]
    nlinarith [hr.2, h0, hA]
  have hint : IntervalIntegrable Φ' volume 0 η :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le).2 (hi1.sub hi2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hη.le hcont
    (fun r hr => hderiv r hr.1) hint
  have hΦη : Φ η = 0 := by simp [hΦ]
  have hΦ0 : Φ 0 = 0 := by simp [hΦ, zero_pow (by omega : d ≠ 0)]
  rw [hΦη, hΦ0, sub_zero, intervalIntegral.integral_of_le hη.le] at hFTC
  have : ∫ r in Ioc (0:ℝ) η, Φ' r = (∫ r in Ioc (0:ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η)) -
      ∫ r in Ioc (0:ℝ) η, r * (kappa d - Aint d l r) / d := integral_sub hi1 hi2
  rw [this] at hFTC
  have h3 : ∫ r in Ioc (0:ℝ) η, r * (kappa d - Aint d l r) / d =
      (1 / d) * ∫ r in Ioc (0:ℝ) η, r * (kappa d - Aint d l r) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun r => by simp only []; ring)
  refine ⟨?_, by linarith⟩
  have : IntegrableOn (fun r : ℝ => (d : ℝ) * (r * (kappa d - Aint d l r) / d)) (Ioc 0 η) := hi2.const_mul (d : ℝ)
  refine this.congr_fun (fun r _ => ?_) measurableSet_Ioc
  field_simp

theorem int_f_bounds (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    (kappa d - Aint d l η) * (η ^ 2 / (2 * d)) ≤
      ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η) ∧
    ∫ r in Ioc (0 : ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η) ≤ kappa d * (η ^ 2 / (2 * d)) := by
  obtain ⟨hint, hform⟩ := int_f_formula hd hl hη
  rw [hform]
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hI : ∫ r in Ioc (0 : ℝ) η, r = η ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hη.le, integral_id]; ring
  have hr : IntegrableOn (fun r : ℝ => r) (Ioc 0 η) := continuous_id.integrableOn_Ioc
  have hA := Aint_nonneg hd hl
  constructor
  · have h1 : ∫ r in Ioc (0 : ℝ) η, r * (kappa d - Aint d l η) ≤ ∫ r in Ioc (0 : ℝ) η, r * (kappa d - Aint d l r) := by
      refine setIntegral_mono_on (hr.mul_const _) hint measurableSet_Ioc fun r hr' => ?_
      have := Aint_mono hd hl hr'.1 hη hr'.2
      nlinarith [hr'.1]
    rw [integral_mul_const, hI] at h1
    calc (kappa d - Aint d l η) * (η ^ 2 / (2 * d)) = (1 / d) * (η ^ 2 / 2 * (kappa d - Aint d l η)) := by
          field_simp
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 1 / d)
          linarith
  · have h1 : ∫ r in Ioc (0 : ℝ) η, r * (kappa d - Aint d l r) ≤ ∫ r in Ioc (0 : ℝ) η, r * kappa d := by
      refine setIntegral_mono_on hint (hr.mul_const _) measurableSet_Ioc fun r hr' => ?_
      nlinarith [hr'.1, hA r]
    rw [integral_mul_const, hI] at h1
    calc (1 / (d:ℝ)) * ∫ r in Ioc (0 : ℝ) η, r * (kappa d - Aint d l r) ≤ (1 / d) * (η ^ 2 / 2 * kappa d) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by field_simp


end HRS.Commutator.SmearAux
