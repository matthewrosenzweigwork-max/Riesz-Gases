/-
# HRS.Equilibrium.MarginalExpFamily -- the exponential family `P.tilted (t * X)` (EQ-02)

Abstract facts on a probability space `(Ω, P)` and a measurable `X ≤ b` (so that `exp (t X)` is
integrable for `t ≥ 0`): derivatives of the cumulant generating function on `(0, ∞)`
(`F' = E_t X`, `F'' = Var_t X`), one-sided limits at `0`, and the two consequences used for the
insertion pressure (`A:eq:insertion-estimates`) and the cavity total variation (`A:eq:cavity-TV`):

* `ef_main`: if `Var_t X ≤ w t` on `(0,1]` with `W = ∫₀¹ w < ∞` then
  `F(1) - E X ≤ W` and `F(1) - 2 F(1/2) ≤ W/2`;
* `tilt_mean_sq_le`: `(E_{R'} φ - E_R φ)² ≤ Var_R(φ) (E_R e^{2ψ} / (E_R e^ψ)² - 1)` for `R' = R.tilted ψ`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

namespace EF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ} {b : ℝ}

theorem integrable_exp_mul (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (t * X ω)) P := by
  refine Integrable.of_bound (C := Real.exp (t * b))
    (Real.measurable_exp.comp (measurable_const.mul hXm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hb ω) ht)

theorem Ioi_subset_interior (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) :
    Ioi (0 : ℝ) ⊆ interior (integrableExpSet X P) :=
  interior_maximal (fun _ ht => integrable_exp_mul hXm hb (le_of_lt ht)) isOpen_Ioi

theorem hasDerivAt_cgf (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cgf X P) ((P.tilted (fun ω => t * X ω))[X]) t := by
  have hint := Ioi_subset_interior (P := P) hXm hb ht
  have h := (analyticAt_cgf hint).differentiableAt.hasDerivAt
  rwa [← integral_tilted_mul_self hint] at h

theorem hasDerivAt_mean (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => (P.tilted (fun ω => u * X ω))[X]) (Var[X; P.tilted (fun ω => t * X ω)]) t := by
  have hint := Ioi_subset_interior (P := P) hXm hb ht
  have h_mem : ∀ᶠ u in 𝓝 t, u ∈ interior (integrableExpSet X P) :=
    isOpen_interior.eventually_mem hint
  have hev : (fun u => (P.tilted (fun ω => u * X ω))[X]) =ᶠ[𝓝 t] deriv (cgf X P) := by
    filter_upwards [h_mem] with u hu using integral_tilted_mul_self hu
  have hd : HasDerivAt (deriv (cgf X P)) (iteratedDeriv 2 (cgf X P) t) t := by
    have : DifferentiableAt ℝ (deriv (cgf X P)) t := (analyticAt_cgf hint).deriv.differentiableAt
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this.hasDerivAt
  rw [variance_tilted_mul hint]
  exact hd.congr_of_eventuallyEq hev

theorem continuousOn_var (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) :
    ContinuousOn (fun t => Var[X; P.tilted (fun ω => t * X ω)]) (Ioi 0) := by
  intro t ht
  have hint := Ioi_subset_interior (P := P) hXm hb ht
  have hc : ContinuousAt (iteratedDeriv 2 (cgf X P)) t := by
    have : AnalyticAt ℝ (deriv (deriv (cgf X P))) t := (analyticAt_cgf hint).deriv.deriv
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using this.continuousAt
  refine (hc.continuousWithinAt).congr (fun u hu => ?_) ?_
  · exact variance_tilted_mul (Ioi_subset_interior (P := P) hXm hb hu)
  · exact variance_tilted_mul hint

/-! ### Limits at `0⁺` -/

theorem tendsto_mgf_zero (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) :
    Tendsto (fun u : ℝ => ∫ ω, Real.exp (u * X ω) ∂P) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝[>] (0 : ℝ))
    (F := fun (u : ℝ) ω => Real.exp (u * X ω)) (f := fun _ => (1 : ℝ))
    (bound := fun _ => Real.exp (max b 0))
    (Filter.Eventually.of_forall fun u =>
      (Real.measurable_exp.comp (measurable_const.mul hXm)).aestronglyMeasurable)
    (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      have h1 : u * X ω ≤ u * b := mul_le_mul_of_nonneg_left (hb ω) hu.1.le
      have h2 : u * b ≤ max b 0 := by
        rcases le_total b 0 with hb0 | hb0
        · have : u * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1.le hb0
          exact this.trans (le_max_right _ _)
        · have : u * b ≤ b := by nlinarith [hu.2]
          exact this.trans (le_max_left _ _)
      linarith)
    (integrable_const _)
    (Filter.Eventually.of_forall fun ω => by
      have : Tendsto (fun u : ℝ => Real.exp (u * X ω)) (𝓝 0) (𝓝 (Real.exp (0 * X ω))) :=
        (Real.continuous_exp.comp (continuous_id.mul continuous_const)).tendsto 0
      simp only [zero_mul, Real.exp_zero] at this
      exact this.mono_left nhdsWithin_le_nhds)
  simpa using h

theorem tendsto_cgf_zero (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) :
    Tendsto (cgf X P) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_log (one_ne_zero)).tendsto.comp (tendsto_mgf_zero (P := P) hXm hb)
  have e : cgf X P = fun u => Real.log (∫ ω, Real.exp (u * X ω) ∂P) := rfl
  rw [e]
  simpa [Function.comp_def] using h

theorem tendsto_mean_zero (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) (hXi : Integrable X P) :
    Tendsto (fun u : ℝ => (P.tilted (fun ω => u * X ω))[X]) (𝓝[>] 0) (𝓝 (P[X])) := by
  have h1 := tendsto_mgf_zero (P := P) hXm hb
  have h2 : Tendsto (fun u : ℝ => ∫ ω, Real.exp (u * X ω) * X ω ∂P) (𝓝[>] 0) (𝓝 (∫ ω, X ω ∂P)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := 𝓝[>] (0 : ℝ))
      (F := fun (u : ℝ) ω => Real.exp (u * X ω) * X ω) (f := fun ω => X ω)
      (bound := fun ω => Real.exp (max b 0) * |X ω|)
      (Filter.Eventually.of_forall fun u =>
        ((Real.measurable_exp.comp (measurable_const.mul hXm)).mul hXm).aestronglyMeasurable)
      (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (abs_nonneg _)
        have h1 : u * X ω ≤ u * b := mul_le_mul_of_nonneg_left (hb ω) hu.1.le
        have h2 : u * b ≤ max b 0 := by
          rcases le_total b 0 with hb0 | hb0
          · have : u * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1.le hb0
            exact this.trans (le_max_right _ _)
          · have : u * b ≤ b := by nlinarith [hu.2]
            exact this.trans (le_max_left _ _)
        linarith)
      (hXi.abs.const_mul _)
      (Filter.Eventually.of_forall fun ω => by
        have : Tendsto (fun u : ℝ => Real.exp (u * X ω) * X ω) (𝓝 0) (𝓝 (Real.exp (0 * X ω) * X ω)) :=
          ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul
            continuous_const).tendsto 0
        simp only [zero_mul, Real.exp_zero, one_mul] at this
        exact this.mono_left nhdsWithin_le_nhds)
    exact h
  have h3 : Tendsto (fun u : ℝ => (∫ ω, Real.exp (u * X ω) ∂P)⁻¹ * ∫ ω, Real.exp (u * X ω) * X ω ∂P)
      (𝓝[>] 0) (𝓝 ((1 : ℝ)⁻¹ * ∫ ω, X ω ∂P)) :=
    (h1.inv₀ one_ne_zero).mul h2
  simp only [inv_one, one_mul] at h3
  refine h3.congr fun u => ?_
  rw [integral_tilted_mul_eq_mgf]
  simp only [smul_eq_mul, div_eq_inv_mul, mul_assoc]
  rw [integral_const_mul]
  rfl

/-! ### The two consequences of a variance bound -/

theorem ef_main (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) (hXi : Integrable X P)
    (w : ℝ → ℝ≥0∞)
    (hw : ∀ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (Var[X; P.tilted (fun ω => t * X ω)]) ≤ w t)
    (hW : ∫⁻ t in Ioc (0 : ℝ) 1, w t ≠ ∞) :
    cgf X P 1 - P[X] ≤ (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal ∧
      cgf X P 1 - 2 * cgf X P (1 / 2) ≤ (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal / 2 := by
  set F := cgf X P with hFdef
  set H : ℝ → ℝ := fun u => (P.tilted (fun ω => u * X ω))[X] with hHdef
  set V : ℝ → ℝ := fun t => Var[X; P.tilted (fun ω => t * X ω)] with hVdef
  set W : ℝ := (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal with hWdef
  set H0 : ℝ := P[X] with hH0def
  have hF : ∀ t, 0 < t → HasDerivAt F (H t) t := fun t ht => hasDerivAt_cgf hXm hb ht
  have hH : ∀ t, 0 < t → HasDerivAt H (V t) t := fun t ht => hasDerivAt_mean hXm hb ht
  have hV0 : ∀ t, 0 ≤ V t := fun t => variance_nonneg _ _
  have hVc : ContinuousOn V (Ioi 0) := continuousOn_var hXm hb
  have hHc : ContinuousOn H (Ioi 0) := fun t ht => (hH t ht).continuousAt.continuousWithinAt
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  -- Step 1
  have step1 : ∀ ε u : ℝ, 0 < ε → ε ≤ u → u ≤ 1 → 0 ≤ H u - H ε ∧ H u - H ε ≤ W := by
    intro ε u hε hεu hu1
    have hsub : Set.uIcc ε u ⊆ Ioi 0 := by
      rw [Set.uIcc_of_le hεu]; intro x hx; exact lt_of_lt_of_le hε hx.1
    have hint : IntervalIntegrable V volume ε u := (hVc.mono hsub).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hH x (hsub hx)) hint
    rw [← hftc]
    refine ⟨intervalIntegral.integral_nonneg hεu fun x _ => hV0 x, ?_⟩
    rw [intervalIntegral.integral_of_le hεu,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hV0)
        ((hVc.mono (fun x hx => lt_of_lt_of_le hε hx.1.le)).aestronglyMeasurable measurableSet_Ioc)]
    refine ENNReal.toReal_mono hW ?_
    calc ∫⁻ x in Ioc ε u, ENNReal.ofReal (V x) ≤ ∫⁻ x in Ioc ε u, w x :=
          setLIntegral_mono' measurableSet_Ioc fun x hx =>
            hw x ⟨lt_of_lt_of_le hε hx.1.le, hx.2.trans hu1⟩
      _ ≤ ∫⁻ x in Ioc (0 : ℝ) 1, w x := lintegral_mono_set (Ioc_subset_Ioc hε.le hu1)
  -- Step 2
  have hlimH : Tendsto H (𝓝[>] 0) (𝓝 H0) := tendsto_mean_zero hXm hb hXi
  have hlimF : Tendsto F (𝓝[>] 0) (𝓝 0) := tendsto_cgf_zero hXm hb
  have step2 : ∀ u : ℝ, 0 < u → u ≤ 1 → H0 ≤ H u ∧ H u ≤ H0 + W := by
    intro u hu hu1
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) u := Ioo_mem_nhdsGT hu
    constructor
    · refine le_of_tendsto hlimH ?_
      filter_upwards [hev] with ε hε
      exact sub_nonneg.1 (step1 ε u hε.1 hε.2.le hu1).1
    · have : H u - W ≤ H0 := by
        refine ge_of_tendsto hlimH ?_
        filter_upwards [hev] with ε hε
        linarith [(step1 ε u hε.1 hε.2.le hu1).2]
      linarith
  -- Step 3: increments of F
  have hHint : ∀ a c : ℝ, 0 < a → a ≤ c → IntervalIntegrable H volume a c := by
    intro a c ha hac
    exact (hHc.mono (by rw [Set.uIcc_of_le hac]; intro x hx; exact lt_of_lt_of_le ha hx.1)).intervalIntegrable
  have hincr : ∀ a c : ℝ, 0 < a → a ≤ c → F c - F a = ∫ x in a..c, H x := by
    intro a c ha hac
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (f' := H) (a := a) (b := c)
      (fun x hx => hF x (by rw [Set.uIcc_of_le hac] at hx; exact lt_of_lt_of_le ha hx.1))
      (hHint a c ha hac)
    exact this.symm
  have a1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → F 1 - F ε ≤ (1 - ε) * (H0 + W) := by
    intro ε hε hε1
    rw [hincr ε 1 hε hε1]
    have := intervalIntegral.integral_mono_on hε1 (hHint ε 1 hε hε1)
      (intervalIntegrable_const (c := H0 + W)) (fun x hx => (step2 x (lt_of_lt_of_le hε hx.1) hx.2).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have a2 : F 1 - F (1 / 2) ≤ (1 / 2) * (H0 + W) := by
    rw [hincr (1 / 2) 1 (by norm_num) (by norm_num)]
    have := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hHint (1 / 2) 1 (by norm_num) (by norm_num))
      (intervalIntegrable_const (c := H0 + W))
      (fun x hx => (step2 x (lt_of_lt_of_le (by norm_num) hx.1) hx.2).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have a3 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (1 / 2 - ε) * H0 ≤ F (1 / 2) - F ε := by
    intro ε hε hε1
    rw [hincr ε (1 / 2) hε hε1]
    have := intervalIntegral.integral_mono_on hε1 (intervalIntegrable_const (c := H0))
      (hHint ε (1 / 2) hε hε1)
      (fun x hx => (step2 x (lt_of_lt_of_le hε hx.1) (hx.2.trans (by norm_num))).1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  constructor
  · -- `F 1 ≤ H0 + W`
    have : F 1 ≤ H0 + W := by
      have hl1 : Tendsto (fun ε => F 1 - F ε) (𝓝[>] 0) (𝓝 (F 1 - 0)) := tendsto_const_nhds.sub hlimF
      have hl2 : Tendsto (fun ε : ℝ => (1 - ε) * (H0 + W)) (𝓝[>] 0) (𝓝 ((1 - 0) * (H0 + W))) :=
        ((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
      have := le_of_tendsto_of_tendsto hl1 hl2 (by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        exact a1 ε hε.1 hε.2.le)
      simpa using this
    linarith
  · have hl1 : Tendsto (fun ε => F 1 - 2 * F (1 / 2) + F ε) (𝓝[>] 0) (𝓝 (F 1 - 2 * F (1 / 2) + 0)) :=
      tendsto_const_nhds.add hlimF
    have hl2 : Tendsto (fun ε : ℝ => W / 2 + ε * H0) (𝓝[>] 0) (𝓝 (W / 2 + 0 * H0)) :=
      tendsto_const_nhds.add (((tendsto_id).mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
    have := le_of_tendsto_of_tendsto hl1 hl2 (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      have h3 := a3 ε hε.1 hε.2.le
      linarith)
    simpa using this


/-! ### Chi-square bound for a tilt -/

theorem cs_integral {μ : Measure Ω} {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have h1 : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have h2 : Integrable (fun ω => g ω ^ 2) μ := hg.integrable_sq
  have h3 : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  have h : ∀ r : ℝ, 0 ≤ (∫ ω, f ω ^ 2 ∂μ) * (r * r) + (-2 * ∫ ω, f ω * g ω ∂μ) * r + ∫ ω, g ω ^ 2 ∂μ := by
    intro r
    have e : ∫ ω, (r * f ω - g ω) ^ 2 ∂μ =
        (∫ ω, f ω ^ 2 ∂μ) * (r * r) + (-2 * ∫ ω, f ω * g ω ∂μ) * r + ∫ ω, g ω ^ 2 ∂μ := by
      have : ∀ ω, (r * f ω - g ω) ^ 2 = (r * r) * f ω ^ 2 + ((-2 * r) * (f ω * g ω) + g ω ^ 2) := fun ω => by ring
      simp_rw [this]
      have i4 : Integrable (fun ω => (-2 * r) * (f ω * g ω) + g ω ^ 2) μ := (h3.const_mul _).add h2
      rw [integral_add (h1.const_mul (r * r)) i4, integral_add (h3.const_mul (-2 * r)) h2,
        integral_const_mul, integral_const_mul]
      ring
    rw [← e]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

theorem tilt_mean_sq_le {Q0 : Measure Ω} [IsProbabilityMeasure Q0] {ψ φ : Ω → ℝ}
    (hψm : Measurable ψ) (hψ1 : Integrable (fun ω => Real.exp (ψ ω)) Q0)
    (hψ2 : Integrable (fun ω => Real.exp (2 * ψ ω)) Q0) {K : ℝ} (hφm : Measurable φ)
    (hφ : ∀ ω, |φ ω| ≤ K) :
    ((∫ ω, φ ω ∂(Q0.tilted ψ)) - (∫ ω, φ ω ∂Q0)) ^ 2 ≤
      Var[φ; Q0] * ((∫ ω, Real.exp (2 * ψ ω) ∂Q0) / (∫ ω, Real.exp (ψ ω) ∂Q0) ^ 2 - 1) := by
  set Z : ℝ := ∫ ω, Real.exp (ψ ω) ∂Q0 with hZ
  have hZ0 : 0 < Z := integral_exp_pos hψ1
  set w : Ω → ℝ := fun ω => Real.exp (ψ ω) / Z with hw
  have hwm : Measurable w := (Real.measurable_exp.comp hψm).div_const _
  have hwi : Integrable w Q0 := hψ1.div_const _
  have hw2 : Integrable (fun ω => w ω ^ 2) Q0 := by
    have : (fun ω => w ω ^ 2) = fun ω => Real.exp (2 * ψ ω) / Z ^ 2 := by
      funext ω
      simp only [hw, div_pow, ← Real.exp_nat_mul]
      norm_num
    rw [this]; exact hψ2.div_const _
  have hwint : ∫ ω, w ω ∂Q0 = 1 := by
    simp only [hw]; rw [integral_div]; exact div_self hZ0.ne'
  have hw2int : ∫ ω, w ω ^ 2 ∂Q0 = (∫ ω, Real.exp (2 * ψ ω) ∂Q0) / Z ^ 2 := by
    have : (fun ω => w ω ^ 2) = fun ω => Real.exp (2 * ψ ω) / Z ^ 2 := by
      funext ω
      simp only [hw, div_pow, ← Real.exp_nat_mul]
      norm_num
    rw [this, integral_div]
  have hφi : Integrable φ Q0 := Integrable.of_bound hφm.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hφ ω)
  have hφ2 : MemLp φ 2 Q0 := MemLp.of_bound hφm.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hφ ω)
  set m : ℝ := ∫ ω, φ ω ∂Q0 with hm
  have hu2 : MemLp (fun ω => w ω - 1) 2 Q0 := by
    refine (memLp_two_iff_integrable_sq ((hwm.sub measurable_const).aestronglyMeasurable)).2 ?_
    have : (fun ω => (w ω - 1) ^ 2) = fun ω => w ω ^ 2 + (-2 * w ω + 1) := by
      funext ω; ring
    show Integrable (fun ω => (w ω - 1) ^ 2) Q0
    rw [this]
    have i5 : Integrable (fun ω => -2 * w ω + 1) Q0 := (hwi.const_mul _).add (integrable_const _)
    exact hw2.add i5
  have hv2 : MemLp (fun ω => φ ω - m) 2 Q0 := hφ2.sub (memLp_const _)
  have hcs := cs_integral hu2 hv2
  -- the left side
  have hlhs : (∫ ω, φ ω ∂(Q0.tilted ψ)) - (∫ ω, φ ω ∂Q0) = ∫ ω, (w ω - 1) * (φ ω - m) ∂Q0 := by
    rw [integral_tilted]
    have e1 : ∫ ω, (Real.exp (ψ ω) / ∫ ω', Real.exp (ψ ω') ∂Q0) • φ ω ∂Q0 = ∫ ω, w ω * φ ω ∂Q0 := by
      simp only [smul_eq_mul, hw, hZ]
    rw [e1]
    have : (fun ω => (w ω - 1) * (φ ω - m)) = fun ω => (w ω * φ ω - φ ω) - (m * w ω - m) := by
      funext ω; ring
    rw [this]
    have iwφ : Integrable (fun ω => w ω * φ ω) Q0 :=
      hwi.mul_bdd hφm.aestronglyMeasurable (c := K)
        (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hφ ω)
    have i1 : Integrable (fun ω => w ω * φ ω - φ ω) Q0 := iwφ.sub hφi
    have i2 : Integrable (fun ω => m * w ω - m) Q0 := (hwi.const_mul m).sub (integrable_const m)
    rw [integral_sub i1 i2, integral_sub iwφ hφi, integral_sub (hwi.const_mul m) (integrable_const m),
      integral_const_mul, hwint]
    simp [hm]
  have hvar : ∫ ω, (φ ω - m) ^ 2 ∂Q0 = Var[φ; Q0] := by
    rw [variance_eq_integral hφm.aemeasurable]
  have hu2int : ∫ ω, (w ω - 1) ^ 2 ∂Q0 = (∫ ω, Real.exp (2 * ψ ω) ∂Q0) / Z ^ 2 - 1 := by
    have : (fun ω => (w ω - 1) ^ 2) = fun ω => w ω ^ 2 + (-2 * w ω + 1) := by
      funext ω; ring
    have i5 : Integrable (fun ω => -2 * w ω + 1) Q0 := (hwi.const_mul _).add (integrable_const _)
    rw [this, integral_add hw2 i5, integral_add (hwi.const_mul _) (integrable_const _),
      integral_const_mul, hwint, hw2int]
    simp
    ring
  rw [hlhs]
  calc (∫ ω, (w ω - 1) * (φ ω - m) ∂Q0) ^ 2
      ≤ (∫ ω, (w ω - 1) ^ 2 ∂Q0) * ∫ ω, (φ ω - m) ^ 2 ∂Q0 := hcs
    _ = _ := by rw [hu2int, hvar]; ring

/-- Total-variation type bound for the tilt `P.tilted X` against `P`, through the intermediate
point `P.tilted (X/2)`: only the variances of `φ` under `P` and under `P.tilted X` and the second
difference `cgf X P 1 - 2 cgf X P (1/2)` enter. -/
theorem ef_tv (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) {φ : Ω → ℝ} {K : ℝ}
    (hφm : Measurable φ) (hφ : ∀ ω, |φ ω| ≤ K) :
    |(∫ ω, φ ω ∂(P.tilted X)) - (∫ ω, φ ω ∂P)| ≤
      (Real.sqrt Var[φ; P] + Real.sqrt Var[φ; P.tilted X]) *
        Real.sqrt (Real.exp (cgf X P 1 - 2 * cgf X P (1 / 2)) - 1) := by
  have hi1 : Integrable (fun ω => Real.exp (1 * X ω)) P := integrable_exp_mul hXm hb zero_le_one
  have hih : Integrable (fun ω => Real.exp ((1 / 2) * X ω)) P :=
    integrable_exp_mul hXm hb (by norm_num)
  set Z1 : ℝ := ∫ ω, Real.exp (1 * X ω) ∂P with hZ1
  set Zh : ℝ := ∫ ω, Real.exp ((1 / 2) * X ω) ∂P with hZh
  have hZ1p : 0 < Z1 := integral_exp_pos hi1
  have hZhp : 0 < Zh := integral_exp_pos hih
  have hcgf1 : cgf X P 1 = Real.log Z1 := rfl
  have hcgfh : cgf X P (1 / 2) = Real.log Zh := rfl
  have hχ : Real.exp (cgf X P 1 - 2 * cgf X P (1 / 2)) = Z1 / Zh ^ 2 := by
    rw [hcgf1, hcgfh, Real.exp_sub, Real.exp_log hZ1p, mul_comm, Real.exp_mul, Real.exp_log hZhp]
    norm_num
  have hX1 : P.tilted X = P.tilted (fun ω => 1 * X ω) := by simp only [one_mul]
  -- (a): P → P.tilted (X/2)
  have hψ1a : Integrable (fun ω => Real.exp ((1 / 2) * X ω)) P := hih
  have hψ2a : Integrable (fun ω => Real.exp (2 * ((1 / 2) * X ω))) P := by
    simpa [← mul_assoc] using hi1
  have ha := tilt_mean_sq_le (Q0 := P) (ψ := fun ω => (1 / 2) * X ω) (φ := φ)
    (measurable_const.mul hXm) hψ1a hψ2a hφm hφ
  have e2a : (∫ ω, Real.exp (2 * ((1 / 2) * X ω)) ∂P) = Z1 := by
    have e : (fun ω => Real.exp (2 * ((1 / 2) * X ω))) = fun ω => Real.exp (1 * X ω) := by
      funext ω; congr 1; ring
    rw [e]
  rw [e2a, ← hZh] at ha
  -- (b): P.tilted X → P.tilted (X/2)
  have hQ1 : IsProbabilityMeasure (P.tilted X) :=
    isProbabilityMeasure_tilted (by simpa using hi1)
  have htt : (P.tilted X).tilted (fun ω => -((1 / 2) * X ω)) = P.tilted (fun ω => (1 / 2) * X ω) := by
    rw [tilted_tilted (by simpa using hi1)]
    congr 1; funext ω; simp only [Pi.add_apply]; ring
  have hint_tilt : ∀ g : Ω → ℝ, ∫ ω, g ω ∂(P.tilted X) = ∫ ω, (Real.exp (X ω) / Z1) * g ω ∂P := by
    intro g
    rw [integral_tilted]
    simp only [smul_eq_mul, one_mul, hZ1]
  have hQi1 : Integrable (fun ω => Real.exp (-((1 / 2) * X ω))) (P.tilted X) := by
    rw [integrable_tilted_iff (by simpa using hi1)]
    refine Integrable.of_bound (C := Real.exp (b / 2))
      ((Real.measurable_exp.comp hXm).mul (Real.measurable_exp.comp
        (measurable_const.mul hXm).neg) |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    simp only [smul_eq_mul, Real.norm_eq_abs]
    rw [← Real.exp_add, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [hb ω])
  have hQi2 : Integrable (fun ω => Real.exp (2 * (-((1 / 2) * X ω)))) (P.tilted X) := by
    rw [integrable_tilted_iff (by simpa using hi1)]
    have : (fun ω => Real.exp (X ω) • Real.exp (2 * (-((1 / 2) * X ω)))) = fun _ => (1 : ℝ) := by
      funext ω
      simp only [smul_eq_mul, ← Real.exp_add]
      rw [show X ω + 2 * (-(1 / 2 * X ω)) = 0 by ring, Real.exp_zero]
    rw [this]; exact integrable_const _
  have hb_ineq := tilt_mean_sq_le (Q0 := P.tilted X) (ψ := fun ω => -((1 / 2) * X ω)) (φ := φ)
    (measurable_const.mul hXm).neg hQi1 hQi2 hφm hφ
  rw [htt] at hb_ineq
  have e1b : (∫ ω, Real.exp (-((1 / 2) * X ω)) ∂(P.tilted X)) = Zh / Z1 := by
    rw [hint_tilt, hZh, ← integral_div]
    congr 1; funext ω
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2; ring
  have e2b : (∫ ω, Real.exp (2 * (-((1 / 2) * X ω))) ∂(P.tilted X)) = 1 / Z1 := by
    rw [hint_tilt]
    have : ∀ ω, Real.exp (X ω) / Z1 * Real.exp (2 * (-((1 / 2) * X ω))) = 1 / Z1 := fun ω => by
      rw [div_mul_eq_mul_div, ← Real.exp_add, show X ω + 2 * (-(1 / 2 * X ω)) = 0 by ring, Real.exp_zero]
    simp_rw [this]
    simp
  rw [e1b, e2b] at hb_ineq
  have hratio : 1 / Z1 / (Zh / Z1) ^ 2 - 1 = Z1 / Zh ^ 2 - 1 := by
    field_simp
  rw [hratio] at hb_ineq
  rw [hχ]
  have hv0 : 0 ≤ Var[φ; P] := variance_nonneg _ _
  have hv1 : 0 ≤ Var[φ; P.tilted X] := variance_nonneg _ _
  have s1 : |(∫ ω, φ ω ∂(P.tilted fun ω => (1 / 2) * X ω)) - ∫ ω, φ ω ∂P| ≤
      Real.sqrt Var[φ; P] * Real.sqrt (Z1 / Zh ^ 2 - 1) := by
    rw [← Real.sqrt_mul hv0]
    exact Real.abs_le_sqrt ha
  have s2 : |(∫ ω, φ ω ∂(P.tilted fun ω => (1 / 2) * X ω)) - ∫ ω, φ ω ∂(P.tilted X)| ≤
      Real.sqrt Var[φ; P.tilted X] * Real.sqrt (Z1 / Zh ^ 2 - 1) := by
    rw [← Real.sqrt_mul hv1]
    exact Real.abs_le_sqrt hb_ineq
  calc |(∫ ω, φ ω ∂(P.tilted X)) - ∫ ω, φ ω ∂P|
      ≤ |(∫ ω, φ ω ∂(P.tilted fun ω => (1 / 2) * X ω)) - ∫ ω, φ ω ∂P| +
        |(∫ ω, φ ω ∂(P.tilted fun ω => (1 / 2) * X ω)) - ∫ ω, φ ω ∂(P.tilted X)| := by
        rw [← abs_neg ((∫ ω, φ ω ∂(P.tilted fun ω => (1 / 2) * X ω)) - ∫ ω, φ ω ∂(P.tilted X))]
        refine (abs_add_le _ _).trans' (le_of_eq ?_)
        congr 1; ring
    _ ≤ _ := by
        rw [add_mul]; exact add_le_add s1 s2


/-- Jensen: `E X ≤ log E e^X`. -/
theorem ef_cgf_ge (hXm : Measurable X) (hb : ∀ ω, X ω ≤ b) (hXi : Integrable X P) :
    P[X] ≤ cgf X P 1 := by
  have hi1 : Integrable (fun ω => Real.exp (1 * X ω)) P := integrable_exp_mul hXm hb zero_le_one
  have hpos : 0 < ∫ ω, Real.exp (1 * X ω) ∂P := integral_exp_pos hi1
  set m : ℝ := P[X] with hm
  have h1 : ∀ ω, Real.exp m * (1 + (X ω - m)) ≤ Real.exp (1 * X ω) := by
    intro ω
    have := Real.add_one_le_exp (X ω - m)
    have h2 : Real.exp (X ω) = Real.exp m * Real.exp (X ω - m) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [one_mul, h2]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h3 : Real.exp m ≤ ∫ ω, Real.exp (1 * X ω) ∂P := by
    have hint : Integrable (fun ω => Real.exp m * (1 + (X ω - m))) P :=
      ((integrable_const 1).add (hXi.sub (integrable_const m))).const_mul _
    have := integral_mono hint hi1 h1
    have e : ∫ ω, Real.exp m * (1 + (X ω - m)) ∂P = Real.exp m := by
      have i2 : Integrable (fun ω => X ω - m) P := hXi.sub (integrable_const m)
      rw [integral_const_mul, integral_add (integrable_const 1) i2, integral_sub hXi (integrable_const m)]
      simp [hm]
    rwa [e] at this
  have : Real.log (Real.exp m) ≤ Real.log (∫ ω, Real.exp (1 * X ω) ∂P) :=
    Real.log_le_log (Real.exp_pos _) h3
  rwa [Real.log_exp] at this

end EF

end MarginalAux

end HRS
