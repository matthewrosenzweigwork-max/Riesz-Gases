import HRS.Energy.Commutator.SmearAuxB

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2), part C: Newton's theorem for the heat kernel

Abstract form of Newton's theorem for `l - Δ`: if a finite measure `ν` and a bounded continuous
function `u` satisfy the weak identity `∫ u (l φ_s - Δ φ_s) = ∫ φ_s dν` for all Gaussians `φ_s`
centred at `z`, then `∫∫_0^∞ e^{-ls} φ_s(y) ds dν(y) = u(z)`
(`newton_lintegral`; proof: Fubini in `(s,y)` on `[t,T]`, the heat equation, approximate identity,
monotone convergence).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators Pointwise
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

/-- the integrand `e^{-ls}(l φ_s - Δφ_s)` of the heat/Green identity -/
def heatInt (d : ℕ) (l : ℝ) (z : Euc d) (s : ℝ) (y : Euc d) : ℝ :=
  Real.exp (-l * s) * (gφ d s z y * (l - ‖y - z‖ ^ 2 / (4 * s ^ 2) + (d : ℝ) / (2 * s)))

theorem heatInt_lap {s : ℝ} (hs : 0 < s) (l : ℝ) (z y : Euc d) :
    heatInt d l z s y = Real.exp (-l * s) * (l * gφ d s z y - lap (gφ d s z) y) := by
  unfold heatInt
  rw [lap_gφ hs]
  ring

theorem heatInt_eq {s : ℝ} (hs : 0 < s) (l : ℝ) (z y : Euc d) :
    heatInt d l z s y = -(Real.exp (-l * s) * SliceAux.gprof d s ‖y - z‖ *
      (-l - (d : ℝ) / (2 * s) + ‖y - z‖ ^ 2 / (4 * s ^ 2))) := by
  unfold heatInt
  rw [gφ_eq]
  ring

theorem integral_heatInt {l : ℝ} {z y : Euc d} {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ s in t..T, heatInt d l z s y =
      Real.exp (-l * t) * gφ d t z y - Real.exp (-l * T) * gφ d T z y := by
  have hd : ∀ s ∈ uIcc t T, HasDerivAt (fun s => -(Real.exp (-l * s) * SliceAux.gprof d s ‖y - z‖))
      (heatInt d l z s y) s := by
    intro s hs
    rw [uIcc_of_le htT] at hs
    have hs0 : 0 < s := lt_of_lt_of_le ht hs.1
    rw [heatInt_eq hs0]
    exact (SliceAux.hasDerivAt_Phi d l hs0 ‖y - z‖).neg
  have hint : IntervalIntegrable (fun s => heatInt d l z s y) volume t T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le htT]
    have hc : ContinuousOn (fun s => -(Real.exp (-l * s) * SliceAux.gprof d s ‖y - z‖ *
        (-l - (d : ℝ) / (2 * s) + ‖y - z‖ ^ 2 / (4 * s ^ 2)))) (Ici t) := by
      have hg := (SliceAux.continuousOn_gprof d (r := ‖y - z‖)).mono (Ici_subset_Ioi.2 ht)
      refine ContinuousOn.neg (ContinuousOn.mul (ContinuousOn.mul (by fun_prop) hg) ?_)
      refine ContinuousOn.add (ContinuousOn.sub continuousOn_const ?_) ?_
      · refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) fun s hs => ?_
        have : 0 < s := lt_of_lt_of_le ht hs
        positivity
      · refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) fun s hs => ?_
        have : 0 < s := lt_of_lt_of_le ht hs
        positivity
    refine (hc.mono Icc_subset_Ici_self).congr fun s hs => ?_
    exact heatInt_eq (lt_of_lt_of_le ht hs.1) l z y
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simp only [gφ_eq]
  ring


theorem gφ_le {t s T : ℝ} (ht : 0 < t) (hts : t ≤ s) (hsT : s ≤ T) (z y : Euc d) :
    gφ d s z y ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * T)) := by
  unfold gφ
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hT : 0 < T := lt_of_lt_of_le hs hsT
  have h1 : (4 * Real.pi * s) ^ (-(d : ℝ) / 2) ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by
      have : (0:ℝ) ≤ d := Nat.cast_nonneg d
      linarith [div_nonneg this (by norm_num : (0:ℝ) ≤ 2)])
  have h2 : Real.exp (-‖y - z‖ ^ 2 / (4 * s)) ≤ Real.exp (-‖y - z‖ ^ 2 / (4 * T)) := by
    apply Real.exp_le_exp.2
    have : ‖y - z‖ ^ 2 / (4 * T) ≤ ‖y - z‖ ^ 2 / (4 * s) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    rw [neg_div, neg_div]; linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

theorem abs_heatInt_le {l : ℝ} (hl : 0 ≤ l) {t s T : ℝ} (ht : 0 < t) (hts : t ≤ s) (hsT : s ≤ T)
    (z y : Euc d) :
    |heatInt d l z s y| ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * T)) *
      (l + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t)) := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  have hg := gφ_pos d hs z y
  have hgl := gφ_le ht hts hsT z y
  unfold heatInt
  have hE : Real.exp (-l * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hr := sq_nonneg ‖y - z‖
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : |l - ‖y - z‖ ^ 2 / (4 * s ^ 2) + (d : ℝ) / (2 * s)| ≤
      l + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t) := by
    have a1 : ‖y - z‖ ^ 2 / (4 * s ^ 2) ≤ ‖y - z‖ ^ 2 / (4 * t ^ 2) :=
      div_le_div_of_nonneg_left hr (by positivity) (by gcongr)
    have a2 : (d : ℝ) / (2 * s) ≤ (d : ℝ) / (2 * t) :=
      div_le_div_of_nonneg_left hd0 (by positivity) (by linarith)
    have a3 : 0 ≤ ‖y - z‖ ^ 2 / (4 * s ^ 2) := by positivity
    have a4 : 0 ≤ (d : ℝ) / (2 * s) := by positivity
    rw [abs_le]; constructor <;> nlinarith [div_nonneg hr (by positivity : (0:ℝ) ≤ 4 * t ^ 2),
      div_nonneg hd0 (by positivity : (0:ℝ) ≤ 2 * t)]
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos hg]
  calc Real.exp (-l * s) * (gφ d s z y * |l - ‖y - z‖ ^ 2 / (4 * s ^ 2) + (d : ℝ) / (2 * s)|)
      ≤ 1 * (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * T))) *
          (l + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t))) := by
        gcongr
    _ = _ := by ring


theorem measurable_heatInt (l : ℝ) (z : Euc d) :
    Measurable (fun p : ℝ × Euc d => heatInt d l z p.1 p.2) := by
  unfold heatInt gφ
  fun_prop

theorem integrable_Gt (hd : 1 ≤ d) (l : ℝ) {t T : ℝ} (ht : 0 < t) (hT : 0 < T) (z : Euc d) :
    Integrable (fun y : Euc d => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * T)) *
      (|l| + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t))) := by
  have hb : 0 < 1 / (4 * T) := by positivity
  have h := ((integrable_pow_gauss hd hb 2).comp_sub_right z).const_mul
    ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (|l| + (d : ℝ) / (2 * t) + 1 / (4 * t ^ 2)))
  refine Integrable.mono' h ?_ (Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Continuous fun y : Euc d => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-‖y - z‖ ^ 2 / (4 * T)) *
      (|l| + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t))).aestronglyMeasurable
  · have hc : 0 < (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have e : Real.exp (-‖y - z‖ ^ 2 / (4 * T)) = Real.exp (-(1 / (4 * T)) * ‖y - z‖ ^ 2) := by
      congr 1; ring
    rw [e]
    have hr := norm_nonneg (y - z)
    have h1 : ‖y - z‖ ^ 2 ≤ (1 + ‖y - z‖) ^ 2 := by nlinarith
    have h2 : (1:ℝ) ≤ (1 + ‖y - z‖) ^ 2 := by nlinarith
    have hE := Real.exp_pos (-(1 / (4 * T)) * ‖y - z‖ ^ 2)
    calc (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * T)) * ‖y - z‖ ^ 2) *
          (|l| + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t))
        ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * T)) * ‖y - z‖ ^ 2) *
          ((|l| + (d : ℝ) / (2 * t) + 1 / (4 * t ^ 2)) * (1 + ‖y - z‖) ^ 2) := by
          gcongr
          have a1 : ‖y - z‖ ^ 2 / (4 * t ^ 2) = 1 / (4 * t ^ 2) * ‖y - z‖ ^ 2 := by ring
          have a2 : 0 ≤ 1 / (4 * t ^ 2) := by positivity
          have a3 : 0 ≤ |l| + (d : ℝ) / (2 * t) := by positivity
          rw [a1]
          nlinarith [mul_le_mul_of_nonneg_left h1 a2, mul_le_mul_of_nonneg_left h2 a3]
      _ = _ := by ring


theorem fubini_heat (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) (z : Euc d) {u : Euc d → ℝ} (hu : Measurable u)
    {M : ℝ} (hM : ∀ y, |u y| ≤ M) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ s in Ioc t T, (∫ y, u y * heatInt d l z s y) =
      ∫ y, (u y * ∫ s in Ioc t T, heatInt d l z s y) := by
  have hT : 0 < T := lt_of_lt_of_le ht htT
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hG := (integrable_Gt hd l ht hT z).const_mul M
  have hint : Integrable (Function.uncurry fun (s : ℝ) (y : Euc d) => u y * heatInt d l z s y)
      ((volume : Measure ℝ).restrict (Ioc t T)|>.prod (volume : Measure (Euc d))) := by
    have hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc t T)) :=
      ⟨by rw [Measure.restrict_apply_univ]; simp⟩
    have h1 := (integrable_const (1:ℝ) (μ := (volume : Measure ℝ).restrict (Ioc t T))).mul_prod hG
    refine Integrable.mono' h1 ?_ ?_
    · exact ((hu.comp measurable_snd).mul (measurable_heatInt l z)).aestronglyMeasurable
    · have : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioc t T)), s ∈ Ioc t T :=
        ae_restrict_mem measurableSet_Ioc
      rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards [this] with s hs
        refine Eventually.of_forall fun y => ?_
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul, one_mul]
        have := abs_heatInt_le hl ht hs.1.le hs.2 z y
        calc |u y| * |heatInt d l z s y| ≤ M * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
            Real.exp (-‖y - z‖ ^ 2 / (4 * T)) * (l + ‖y - z‖ ^ 2 / (4 * t ^ 2) + (d : ℝ) / (2 * t))) :=
              mul_le_mul (hM y) this (abs_nonneg _) hM0
          _ = _ := by rw [abs_of_nonneg hl]
      · refine measurableSet_le ?_ ?_
        · exact ((hu.comp measurable_snd).mul (measurable_heatInt l z)).norm
        · fun_prop
  refine (integral_integral_swap hint).trans ?_
  congr 1
  funext y
  rw [integral_const_mul]


theorem newton_E (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (z : Euc d) {u : Euc d → ℝ} (hu : Measurable u)
    {M : ℝ} (hM : ∀ y, |u y| ≤ M) (ν : Measure (Euc d)) [IsFiniteMeasure ν]
    (hW : ∀ s : ℝ, 0 < s → ∫ y, u y * (l * gφ d s z y - lap (gφ d s z) y) = ∫ y, gφ d s z y ∂ν)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ y, (∫ s in Ioc t T, Real.exp (-l * s) * gφ d s z y) ∂ν =
      ∫ y, u y * (Real.exp (-l * t) * gφ d t z y - Real.exp (-l * T) * gφ d T z y) := by
  have hT : 0 < T := lt_of_lt_of_le ht htT
  -- step 1: swap on the ν side
  have hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc t T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have hmeas : Measurable (fun p : Euc d × ℝ => Real.exp (-l * p.2) * gφ d p.2 z p.1) := by
    unfold gφ; fun_prop
  have hint : Integrable (Function.uncurry fun (y : Euc d) (s : ℝ) => Real.exp (-l * s) * gφ d s z y)
      (ν.prod ((volume : Measure ℝ).restrict (Ioc t T))) := by
    refine Integrable.mono' (integrable_const ((4 * Real.pi * t) ^ (-(d : ℝ) / 2))) hmeas.aestronglyMeasurable ?_
    rw [Measure.ae_prod_iff_ae_ae]
    · refine Eventually.of_forall fun y => ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
      have hs0 : 0 < s := lt_trans ht hs.1
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (gφ_pos d hs0 z y).le)]
      have hE : Real.exp (-l * s) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have := gφ_le ht hs.1.le hs.2 z y
      have h2 : Real.exp (-‖y - z‖ ^ 2 / (4 * T)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ ‖y - z‖ ^ 2 / (4 * T) := by positivity
        rw [neg_div]; linarith
      calc Real.exp (-l * s) * gφ d s z y ≤ 1 * gφ d s z y :=
            mul_le_mul_of_nonneg_right hE (gφ_pos d hs0 z y).le
        _ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * 1 := by
            rw [one_mul]
            exact this.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = _ := mul_one _
    · refine measurableSet_le ?_ measurable_const
      exact hmeas.norm
  have step1 := integral_integral_swap hint
  rw [step1]
  have step2 : ∀ s ∈ Ioc t T, ∫ y, Real.exp (-l * s) * gφ d s z y ∂ν = ∫ y, u y * heatInt d l z s y := by
    intro s hs
    have hs0 : 0 < s := lt_trans ht hs.1
    rw [integral_const_mul, ← hW s hs0]
    simp_rw [heatInt_lap hs0, ← mul_assoc, mul_comm (u _) (Real.exp _), mul_assoc]
    rw [integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Ioc step2, fubini_heat hd hl.le z hu hM ht htT]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show u y * ∫ s in Ioc t T, heatInt d l z s y = _
  rw [← intervalIntegral.integral_of_le htT, integral_heatInt ht htT]


theorem integrable_gφ (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (z : Euc d) : Integrable (gφ d s z) := by
  have hb : 0 < 1 / (4 * s) := by positivity
  have h := ((integrable_pow_gauss hd hb 0).comp_sub_right z).const_mul ((4 * Real.pi * s) ^ (-(d : ℝ) / 2))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [pow_zero, one_mul, Function.comp, gφ]
  congr 2; ring

theorem integral_gφ (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (z : Euc d) : ∫ y, gφ d s z y = 1 :=
  integral_gauss_one hd hs z

theorem gφ_tail {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (z y : Euc d) (hy : δ ≤ ‖y - z‖) :
    gφ d t z y ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y := by
  unfold gφ
  have h1 : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) = (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) := by
    have e : 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) := by ring
    rw [e, Real.mul_rpow (x := 2) (y := 4 * Real.pi * t) (by norm_num) (by positivity), ← mul_assoc]
    have : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      have : (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    rw [this, one_mul]
  have h2 : Real.exp (-‖y - z‖ ^ 2 / (4 * t)) ≤ Real.exp (-δ ^ 2 / (8 * t)) * Real.exp (-‖y - z‖ ^ 2 / (4 * (2 * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have : δ ^ 2 ≤ ‖y - z‖ ^ 2 := pow_le_pow_left₀ hδ.le hy 2
    have e1 : -‖y - z‖ ^ 2 / (4 * t) = -δ ^ 2 / (8 * t) + -‖y - z‖ ^ 2 / (4 * (2 * t)) +
        (δ ^ 2 - ‖y - z‖ ^ 2) / (8 * t) := by field_simp; ring
    rw [e1]
    have : (δ ^ 2 - ‖y - z‖ ^ 2) / (8 * t) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  rw [h1]
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * t))
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) *
        (Real.exp (-δ ^ 2 / (8 * t)) * Real.exp (-‖y - z‖ ^ 2 / (4 * (2 * t)))) := by gcongr
    _ = _ := by ring


theorem approx_id (hd : 1 ≤ d) (z : Euc d) {u : Euc d → ℝ} (hu : Measurable u)
    {M : ℝ} (hM : ∀ y, |u y| ≤ M) (hcont : ContinuousAt u z) :
    Tendsto (fun t : ℝ => ∫ y, u y * gφ d t z y) (𝓝[>] 0) (𝓝 (u z)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by linarith)
  set C : ℝ := 2 * M * (2 : ℝ) ^ ((d : ℝ) / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-δ ^ 2 / (8 * t))) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => (-δ ^ 2 / 8) * t⁻¹) (𝓝[>] 0) atBot :=
      (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop_of_neg (by nlinarith)
    have h1 : Tendsto (fun t : ℝ => -δ ^ 2 / (8 * t)) (𝓝[>] 0) atBot := by
      refine h0.congr (fun t => ?_)
      field_simp
    have h3 := (Real.tendsto_exp_atBot.comp h1).const_mul C
    simpa using h3
  have hev := (tendsto_order.1 hlim).2 (ε / 2) (by linarith)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
  have ht0' : (0:ℝ) < t := ht0
  rw [Real.dist_eq]
  have hφ1 := integral_gφ hd ht0' z
  have hI1 : Integrable (fun y => u y * gφ d t z y) := by
    refine (integrable_gφ hd ht0' z).bdd_mul (c := M) hu.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simpa using hM y
  have hI2 : Integrable (fun y => u z * gφ d t z y) := (integrable_gφ hd ht0' z).const_mul (u z)
  have hint : (∫ y, u y * gφ d t z y) - u z = ∫ y, (u y - u z) * gφ d t z y := by
    have e : ∀ y, (u y - u z) * gφ d t z y = u y * gφ d t z y - u z * gφ d t z y := fun y => by ring
    simp_rw [e]
    rw [integral_sub hI1 hI2, integral_const_mul, hφ1, mul_one]
  rw [hint]
  have hg2 : Integrable (gφ d (2 * t) z) := integrable_gφ hd (by positivity) z
  have hbound : ∀ y, |(u y - u z) * gφ d t z y| ≤
      ε / 2 * gφ d t z y + C * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y := by
    intro y
    have hg := gφ_pos d ht0' z y
    have hg2' := gφ_pos d (by positivity : (0:ℝ) < 2 * t) z y
    rw [abs_mul, abs_of_pos hg]
    by_cases hy : ‖y - z‖ < δ
    · have := hδu (show dist y z < δ by simpa [dist_eq_norm] using hy)
      rw [Real.dist_eq] at this
      have : |u y - u z| * gφ d t z y ≤ ε / 2 * gφ d t z y := mul_le_mul_of_nonneg_right this.le hg.le
      have h2 : 0 ≤ C * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y := by positivity
      linarith
    · push_neg at hy
      have h1 : |u y - u z| ≤ 2 * M := by
        calc |u y - u z| ≤ |u y| + |u z| := abs_sub _ _
          _ ≤ M + M := add_le_add (hM y) (hM z)
          _ = 2 * M := by ring
      have h2 := gφ_tail ht0' hδ z y hy
      have h3 : |u y - u z| * gφ d t z y ≤ (2 * M) * ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y) :=
        mul_le_mul h1 h2 hg.le (by positivity)
      have h4 : 0 ≤ ε / 2 * gφ d t z y := by positivity
      calc |u y - u z| * gφ d t z y ≤ _ := h3
        _ = C * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y := by rw [hC]; ring
        _ ≤ _ := by linarith
  have hi1 : Integrable (fun y => (u y - u z) * gφ d t z y) := by
    refine (hI1.sub hI2).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  calc |∫ y, (u y - u z) * gφ d t z y| ≤ ∫ y, |(u y - u z) * gφ d t z y| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => (u y - u z) * gφ d t z y)
    _ ≤ ∫ y, (ε / 2 * gφ d t z y + C * Real.exp (-δ ^ 2 / (8 * t)) * gφ d (2 * t) z y) :=
        integral_mono hi1.abs (((integrable_gφ hd ht0' z).const_mul _).add (hg2.const_mul _)) hbound
    _ = ε / 2 + C * Real.exp (-δ ^ 2 / (8 * t)) := by
        rw [integral_add ((integrable_gφ hd ht0' z).const_mul _) (hg2.const_mul _), integral_const_mul,
          integral_const_mul, hφ1, integral_gφ hd (by positivity) z]
        ring
    _ < ε := by linarith


/-- the time cut-offs `t_n = 1/(n+2)`, `T_n = n+2` -/
def tseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
def Tseq (n : ℕ) : ℝ := (n : ℝ) + 2

theorem tseq_pos (n : ℕ) : 0 < tseq n := by unfold tseq; positivity
theorem Tseq_pos (n : ℕ) : 0 < Tseq n := by unfold Tseq; positivity
theorem tseq_le_Tseq (n : ℕ) : tseq n ≤ Tseq n := by
  unfold tseq Tseq
  have : (1:ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  rw [div_le_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
theorem tseq_anti : Antitone tseq := by
  intro m n hmn
  unfold tseq
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  gcongr
theorem Tseq_mono : Monotone Tseq := by
  intro m n hmn
  unfold Tseq
  have : (m : ℝ) ≤ n := by exact_mod_cast hmn
  linarith

theorem tendsto_tseq : Tendsto tseq atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => tseq_pos n⟩
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  refine this.congr (fun n => ?_)
  simp only [Function.comp, tseq]
  push_cast; ring_nf

theorem tendsto_Tseq : Tendsto Tseq atTop atTop := by
  unfold Tseq
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds

theorem iUnion_Ioc_seq : (⋃ n, Ioc (tseq n) (Tseq n)) = Ioi 0 := by
  ext s
  simp only [mem_iUnion, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩; exact lt_trans (tseq_pos n) h1
  · intro hs
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / s) s)
    refine ⟨n, ?_, ?_⟩
    · unfold tseq
      have h1 : 1 / s < n := lt_of_le_of_lt (le_max_left _ _) hn
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hs] at h1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · unfold Tseq
      have h1 : s < n := lt_of_le_of_lt (le_max_right _ _) hn
      linarith


theorem tendsto_R (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (z : Euc d) {u : Euc d → ℝ} (hu : Continuous u)
    {M : ℝ} (hM : ∀ y, |u y| ≤ M) :
    Tendsto (fun n : ℕ => ∫ y, u y * (Real.exp (-l * tseq n) * gφ d (tseq n) z y -
      Real.exp (-l * Tseq n) * gφ d (Tseq n) z y)) atTop (𝓝 (u z)) := by
  have hI : ∀ s : ℝ, 0 < s → Integrable (fun y => u y * gφ d s z y) := fun s hs =>
    (integrable_gφ hd hs z).bdd_mul (c := M) hu.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using hM y)
  have e : ∀ n : ℕ, ∫ y, u y * (Real.exp (-l * tseq n) * gφ d (tseq n) z y -
      Real.exp (-l * Tseq n) * gφ d (Tseq n) z y) =
      Real.exp (-l * tseq n) * (∫ y, u y * gφ d (tseq n) z y) -
        Real.exp (-l * Tseq n) * (∫ y, u y * gφ d (Tseq n) z y) := by
    intro n
    have h1 := (hI _ (tseq_pos n)).const_mul (Real.exp (-l * tseq n))
    have h2 := (hI _ (Tseq_pos n)).const_mul (Real.exp (-l * Tseq n))
    have : ∀ y, u y * (Real.exp (-l * tseq n) * gφ d (tseq n) z y - Real.exp (-l * Tseq n) * gφ d (Tseq n) z y) =
        Real.exp (-l * tseq n) * (u y * gφ d (tseq n) z y) - Real.exp (-l * Tseq n) * (u y * gφ d (Tseq n) z y) :=
      fun y => by ring
    simp_rw [this]
    rw [integral_sub h1 h2, integral_const_mul, integral_const_mul]
  simp_rw [e]
  have a1 : Tendsto (fun n : ℕ => Real.exp (-l * tseq n)) atTop (𝓝 1) := by
    have h0 : Tendsto tseq atTop (𝓝 0) := tendsto_tseq.mono_right nhdsWithin_le_nhds
    have h : Tendsto (fun n : ℕ => -l * tseq n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := -l)).mul h0
    have := (Real.continuous_exp.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have a2 : Tendsto (fun n : ℕ => ∫ y, u y * gφ d (tseq n) z y) atTop (𝓝 (u z)) :=
    (approx_id hd z hu.measurable hM hu.continuousAt).comp tendsto_tseq
  have a3 : Tendsto (fun n : ℕ => Real.exp (-l * Tseq n) * (∫ y, u y * gφ d (Tseq n) z y)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => Real.exp (-l * Tseq n)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => -l * Tseq n) atTop atBot :=
        tendsto_Tseq.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp this
    have hb' : Tendsto (fun n : ℕ => Real.exp (-l * Tseq n) * M) atTop (𝓝 0) := by
      simpa using hb.mul_const M
    refine squeeze_zero_norm (fun n => ?_) hb'
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have hT := Tseq_pos n
    calc |∫ y, u y * gφ d (Tseq n) z y| ≤ ∫ y, |u y * gφ d (Tseq n) z y| := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => u y * gφ d (Tseq n) z y)
      _ ≤ ∫ y, M * gφ d (Tseq n) z y := by
          refine integral_mono (hI _ hT).abs ((integrable_gφ hd hT z).const_mul M) fun y => ?_
          rw [abs_mul, abs_of_pos (gφ_pos d hT z y)]
          exact mul_le_mul_of_nonneg_right (hM y) (gφ_pos d hT z y).le
      _ = M := by rw [integral_const_mul, integral_gφ hd hT z, mul_one]
  have h := (a1.mul a2).sub a3
  simpa only [one_mul, sub_zero] using h


theorem newton_lintegral (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) (z : Euc d) {u : Euc d → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M) (ν : Measure (Euc d)) [IsFiniteMeasure ν]
    (hW : ∀ s : ℝ, 0 < s → ∫ y, u y * (l * gφ d s z y - lap (gφ d s z) y) = ∫ y, gφ d s z y ∂ν) :
    ∫⁻ y, (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-l * s) * gφ d s z y)) ∂ν =
      ENNReal.ofReal (u z) := by
  have hmeas : Measurable (fun p : Euc d × ℝ => Real.exp (-l * p.2) * gφ d p.2 z p.1) := by
    unfold gφ; fun_prop
  set K : ℕ → Euc d → ℝ := fun n y => ∫ s in Ioc (tseq n) (Tseq n), Real.exp (-l * s) * gφ d s z y with hK
  have hgc : ∀ y : Euc d, ContinuousOn (fun s : ℝ => Real.exp (-l * s) * gφ d s z y) (Ioi 0) := by
    intro y
    have h1 : ContinuousOn (fun s : ℝ => Real.exp (-l * s)) (Ioi 0) := by fun_prop
    have h2 : ContinuousOn (fun s : ℝ => gφ d s z y) (Ioi 0) := by
      have := (SliceAux.continuousOn_gprof d (r := ‖y - z‖))
      exact this
    exact h1.mul h2
  have hgnn : ∀ (y : Euc d) (s : ℝ), 0 < s → 0 ≤ Real.exp (-l * s) * gφ d s z y := fun y s hs =>
    mul_nonneg (Real.exp_pos _).le (gφ_pos d hs z y).le
  have hInt : ∀ n y, IntegrableOn (fun s : ℝ => Real.exp (-l * s) * gφ d s z y) (Ioc (tseq n) (Tseq n)) := by
    intro n y
    have : ContinuousOn (fun s : ℝ => Real.exp (-l * s) * gφ d s z y) (Icc (tseq n) (Tseq n)) :=
      (hgc y).mono (fun s hs => lt_of_lt_of_le (tseq_pos n) hs.1)
    exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hKeq : ∀ n y, ENNReal.ofReal (K n y) =
      ∫⁻ s in Ioc (tseq n) (Tseq n), ENNReal.ofReal (Real.exp (-l * s) * gφ d s z y) := by
    intro n y
    rw [hK]
    simp only []
    rw [ofReal_integral_eq_lintegral_ofReal (hInt n y)]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    exact hgnn y s (lt_trans (tseq_pos n) hs.1)
  have hKnn : ∀ n y, 0 ≤ K n y := fun n y =>
    setIntegral_nonneg measurableSet_Ioc fun s hs => hgnn y s (lt_trans (tseq_pos n) hs.1)
  have hKmeas : ∀ n, Measurable (K n) := by
    intro n
    have := (show StronglyMeasurable (Function.uncurry fun (y : Euc d) (s : ℝ) => Real.exp (-l * s) * gφ d s z y)
      from hmeas.stronglyMeasurable).integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioc (tseq n) (Tseq n)))
    exact this.measurable
  have hset : Directed (· ⊆ ·) (fun n => Ioc (tseq n) (Tseq n)) := by
    refine Monotone.directed_le ?_
    intro m n hmn
    exact Ioc_subset_Ioc (tseq_anti hmn) (Tseq_mono hmn)
  have hKsup : ∀ y, ⨆ n, ENNReal.ofReal (K n y) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-l * s) * gφ d s z y) := by
    intro y
    simp_rw [hKeq]
    rw [← setLIntegral_iUnion_of_directed _ hset, iUnion_Ioc_seq]
  have hKmono : Monotone (fun n y => ENNReal.ofReal (K n y)) := by
    intro m n hmn y
    simp only []
    rw [hKeq, hKeq]
    exact lintegral_mono_set (Ioc_subset_Ioc (tseq_anti hmn) (Tseq_mono hmn))
  have hKint' : ∀ n, Integrable (K n) ν := by
    intro n
    have ht := tseq_pos n
    refine Integrable.mono' (integrable_const ((4 * Real.pi * tseq n) ^ (-(d : ℝ) / 2) * (Tseq n - tseq n)))
      (hKmeas n).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnn n y)]
    have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Ioc (tseq n) (Tseq n))
      (f := fun s : ℝ => Real.exp (-l * s) * gφ d s z y)
      (C := (4 * Real.pi * tseq n) ^ (-(d : ℝ) / 2)) (by simp) (fun s hs => by
        have hs0 : 0 < s := lt_trans ht hs.1
        rw [Real.norm_eq_abs, abs_of_nonneg (hgnn y s hs0)]
        have hE : Real.exp (-l * s) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
        have h1 := gφ_le ht hs.1.le hs.2 z y
        have h2 : Real.exp (-‖y - z‖ ^ 2 / (4 * Tseq n)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ ‖y - z‖ ^ 2 / (4 * Tseq n) := by have := Tseq_pos n; positivity
          rw [neg_div]; linarith
        calc Real.exp (-l * s) * gφ d s z y ≤ 1 * gφ d s z y :=
              mul_le_mul_of_nonneg_right hE (gφ_pos d hs0 z y).le
          _ ≤ _ := by
            rw [one_mul]
            exact h1.trans (by
              calc (4 * Real.pi * tseq n) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * Tseq n))
                  ≤ (4 * Real.pi * tseq n) ^ (-(d : ℝ) / 2) * 1 := by gcongr
                _ = _ := mul_one _))
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnn n y)] at this
    calc K n y ≤ _ := this
      _ = _ := by
        have h3 : (volume : Measure ℝ).real (Ioc (tseq n) (Tseq n)) = Tseq n - tseq n := by
          simp [Real.volume_real_Ioc, tseq_le_Tseq n]
        rw [h3]
  -- the integrals
  have hKint : ∀ n, ∫⁻ y, ENNReal.ofReal (K n y) ∂ν = ENNReal.ofReal (∫ y, u y * (Real.exp (-l * tseq n) *
      gφ d (tseq n) z y - Real.exp (-l * Tseq n) * gφ d (Tseq n) z y)) := by
    intro n
    rw [← newton_E hd hl z hu.measurable hM ν hW (tseq_pos n) (tseq_le_Tseq n)]
    exact (ofReal_integral_eq_lintegral_ofReal (hKint' n) (Eventually.of_forall (hKnn n))).symm
  simp_rw [← hKsup]
  rw [lintegral_iSup (fun n => (hKmeas n).ennreal_ofReal) hKmono]
  simp_rw [hKint]
  have hmono2 : Monotone (fun n => ENNReal.ofReal (∫ y, u y * (Real.exp (-l * tseq n) *
      gφ d (tseq n) z y - Real.exp (-l * Tseq n) * gφ d (Tseq n) z y))) := by
    intro m n hmn
    simp only []
    rw [← hKint, ← hKint]
    exact lintegral_mono fun y => hKmono hmn y
  have hlim := (ENNReal.tendsto_ofReal (tendsto_R hd hl z hu hM))
  exact (tendsto_nhds_unique (tendsto_atTop_iSup hmono2) hlim)

end HRS.Commutator.SmearAux
