import HRS.MS.S113X2B8

/-! # S11.3 X2 part B, B9: the power chain inequality for absolutely continuous exponents

Approximate `p'` in `L¹(0,T)` by continuous `ψ_k`, set `p_k = p 0 + ∫ ψ_k` (`C¹`), apply `s113b_chain_C1`
and pass to the limit (dominated convergence in `x`, then in `τ`; the term `ψ_k c_k → p' c` uses `L¹` convergence). -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.S113X2B

/-- The numerator of `s113b_R`. -/
def s113b_N {n : ℕ} (ν : ℝ) (b : s113b_E n → s113b_E n) (q : ℝ → s113b_E n → ℝ) (τ : ℝ) (x : s113b_E n) : ℝ :=
  ν * s113b_lap (q τ) x - s113b_div (fun y => q τ y • b y) x - deriv (fun σ => q σ x) τ

theorem s113b_N_contB9 {n : ℕ} (ν : ℝ) {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ}
    (hb : ContDiff ℝ 2 b) (hq : ContDiff ℝ 2 (fun z : ℝ × s113b_E n => q z.1 z.2)) :
    Continuous (fun z : ℝ × s113b_E n => s113b_N ν b q z.1 z.2) := by
  have hh : ContDiff ℝ 2 (fun p : (ℝ × s113b_E n) × s113b_E n => q p.1.1 p.2) :=
    hq.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have h1 : ContDiff ℝ 1 (fun z : ℝ × s113b_E n => fderiv ℝ (q z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) y => q z.1 y) (g := Prod.snd) hh contDiff_snd (by norm_num)
  have h2 : Continuous (fun z : ℝ × s113b_E n => fderiv ℝ (fderiv ℝ (q z.1)) z.2) :=
    (ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) y => fderiv ℝ (q z.1) y) (g := Prod.snd) (m := 1) (n := 0)
      (h1.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous
  have h3 : ∀ k, Continuous (fun z : ℝ × s113b_E n => fderiv ℝ (fun y => q z.1 y * b y k) z.2) := fun k =>
    (ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) y => q z.1 y * b y k) (g := Prod.snd) (m := 2) (n := 0)
      (hh.mul (((EuclideanSpace.proj k : s113b_E n →L[ℝ] ℝ).contDiff.comp hb).comp contDiff_snd))
      contDiff_snd (by norm_num)).continuous
  have h4 : Continuous (fun z : ℝ × s113b_E n => fderiv ℝ (fun σ => q σ z.2) z.1) :=
    (ContDiff.fderiv (f := fun (z : ℝ × s113b_E n) σ => q σ z.2) (g := Prod.fst) (m := 2) (n := 0)
      (hq.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst (by norm_num)).continuous
  simp only [s113b_N, s113b_lap, s113b_div, PiLp.smul_apply, smul_eq_mul]
  refine ((continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)).sub
    (continuous_finsetSum _ fun k _ => ?_)).sub ?_
  · exact (h2.clm_apply continuous_const).clm_apply continuous_const
  · exact (h3 k).clm_apply continuous_const
  · exact h4.clm_apply continuous_const


theorem s113b_param {n : ℕ} {K : Set (s113b_E n)} (hK : IsCompact K) {a b C : ℝ} {H : ℝ → s113b_E n → ℝ}
    (hm : ∀ e, AEStronglyMeasurable (H e) volume)
    (hb : ∀ e ∈ Icc a b, ∀ x, ‖H e x‖ ≤ K.indicator (fun _ => C) x)
    (hc : ∀ x, ContinuousOn (fun e => H e x) (Icc a b)) :
    ContinuousOn (fun e => ∫ x, H e x) (Icc a b) ∧ ∀ e ∈ Icc a b, |∫ x, H e x| ≤ C * (volume K).toReal := by
  have hi : Integrable (K.indicator fun _ => C) (volume : Measure (s113b_E n)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  refine ⟨continuousOn_of_dominated (fun e _ => hm e) (fun e he => ae_of_all _ (hb e he)) hi
    (ae_of_all _ hc), fun e he => ?_⟩
  have := norm_integral_le_of_norm_le hi (ae_of_all _ (hb e he))
  rwa [integral_indicator_const _ hK.measurableSet, Real.norm_eq_abs, smul_eq_mul, mul_comm] at this

theorem s113b_ratio {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B) :
    ∃ Z, 0 ≤ Z ∧ ∀ τ ∈ Icc 0 T, ∀ x, u τ x / q τ x ∈ Icc 0 Z := by
  obtain ⟨qm, hqm, hle⟩ := (isCompact_Icc.prod hD.hKc).exists_forall_le' (a := 0)
    (f := fun z : ℝ × s113b_E n => q z.1 z.2) hD.hq.continuous.continuousOn
    (fun z hz => hD.hq0 _ hz.1 _)
  refine ⟨|B| / qm, by positivity, fun τ hτ x => ⟨div_nonneg (hD.hu0 _ _) (hD.hq0 _ hτ _).le, ?_⟩⟩
  by_cases hx : x ∈ K
  · exact div_le_div₀ (abs_nonneg _) ((hD.huB _ hτ x).trans (le_abs_self _)) hqm (hle (τ, x) ⟨hτ, hx⟩)
  · simp [hD.hKu _ _ hx]; positivity

theorem s113b_fam {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    {w : ℝ → s113b_E n → ℝ} (hw : Continuous (fun z : ℝ × s113b_E n => w z.1 z.2))
    {φ : ℝ → ℝ → ℝ} {a b' Z : ℝ} (hr : ∀ τ ∈ Icc 0 T, ∀ x, u τ x / q τ x ∈ Icc 0 Z)
    (hφm : Measurable (fun y : ℝ × ℝ => φ y.1 y.2))
    (hφ : ∃ Cφ, (∀ e ∈ Icc a b', φ e 0 = 0) ∧ (∀ e ∈ Icc a b', ∀ z ∈ Icc 0 Z, |φ e z| ≤ Cφ) ∧
      ∀ z, 0 ≤ z → ContinuousOn (fun e => φ e z) (Icc a b')) :
    (∀ τ ∈ Icc 0 T, ContinuousOn (fun e => ∫ x, w τ x * φ e (u τ x / q τ x)) (Icc a b')) ∧
    (∃ C, ∀ τ ∈ Icc 0 T, ∀ e ∈ Icc a b', |∫ x, w τ x * φ e (u τ x / q τ x)| ≤ C) ∧
    ∀ e : ℝ → ℝ, Continuous e → AEStronglyMeasurable (fun τ => ∫ x, w τ x * φ (e τ) (u τ x / q τ x)) volume := by
  obtain ⟨Cφ, h0, hb, hc⟩ := hφ
  obtain ⟨W, hW⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := T)).prod hD.hKc).exists_bound_of_continuousOn hw.continuousOn
  have hqc : Continuous (fun z : ℝ × s113b_E n => q z.1 z.2) := hD.hq.continuous
  have hmeas : ∀ e : ℝ → ℝ, Continuous e → Measurable (fun z : ℝ × s113b_E n =>
      w z.1 z.2 * φ (e z.1) (u z.1 z.2 / q z.1 z.2)) := fun e he =>
    hw.measurable.mul (hφm.comp ((he.measurable.comp measurable_fst).prodMk (hD.hum.div hqc.measurable)))
  have key : ∀ τ ∈ Icc 0 T, ContinuousOn (fun e => ∫ x, w τ x * φ e (u τ x / q τ x)) (Icc a b') ∧
      ∀ e ∈ Icc a b', |∫ x, w τ x * φ e (u τ x / q τ x)| ≤ (W * Cφ) * (volume K).toReal := by
    intro τ hτ
    refine s113b_param (H := fun e x => w τ x * φ e (u τ x / q τ x)) hD.hKc ?_ ?_ ?_
    · intro e
      exact ((hmeas (fun _ => e) continuous_const).comp (measurable_prodMk_left (x := τ))).aestronglyMeasurable
    · intro e he x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul]
        have hWx : |w τ x| ≤ W := hW (τ, x) ⟨hτ, hx⟩
        exact mul_le_mul hWx (hb e he _ (hr τ hτ x)) (abs_nonneg _) ((abs_nonneg _).trans hWx)
      · simp [indicator_of_notMem hx, hD.hKu _ _ hx, h0 e he]
    · intro x
      exact continuousOn_const.mul (hc _ (hr τ hτ x).1)
  exact ⟨fun τ hτ => (key τ hτ).1, ⟨_, fun τ hτ e he => (key τ hτ).2 e he⟩, fun e he =>
    ((hmeas e he).stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable⟩


theorem s113b_pow_props (a b Z : ℝ) (ha : 0 < a) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, (∀ e ∈ Icc a b, (0:ℝ) ^ e = 0) ∧ (∀ e ∈ Icc a b, ∀ z ∈ Icc (0:ℝ) Z, |z ^ e| ≤ C) ∧
      ∀ z : ℝ, 0 ≤ z → ContinuousOn (fun e : ℝ => z ^ e) (Icc a b) := by
  refine ⟨(Z + 1) ^ b, fun e he => Real.zero_rpow (by linarith [he.1]), fun e he z hz => ?_,
    fun z _ e he => (Real.continuousAt_const_rpow' (by linarith [he.1])).continuousWithinAt⟩
  rw [abs_of_nonneg (Real.rpow_nonneg hz.1 _)]
  exact (Real.rpow_le_rpow hz.1 (hz.2.trans (by linarith)) (by linarith [he.1])).trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) he.2)

theorem s113b_log_props (a b Z : ℝ) (ha : 0 < a) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, (∀ e ∈ Icc a b, (0:ℝ) ^ e * Real.log 0 = 0) ∧
      (∀ e ∈ Icc a b, ∀ z ∈ Icc (0:ℝ) Z, |z ^ e * Real.log z| ≤ C) ∧
      ∀ z : ℝ, 0 ≤ z → ContinuousOn (fun e : ℝ => z ^ e * Real.log z) (Icc a b) := by
  have hlog : 0 ≤ Real.log (Z + 1) := Real.log_nonneg (by linarith)
  refine ⟨1 / a + (Z + 1) ^ b * Real.log (Z + 1), fun e _ => by simp, fun e he z hz => ?_, fun z hz => ?_⟩
  · rcases hz.1.eq_or_lt with h | h
    · subst h; simp; positivity
    · exact s113b_xlog_bound h (hz.2.trans (by linarith)) (by linarith) ha he.1 he.2
  · have : ContinuousOn (fun e : ℝ => z ^ e) (Icc a b) := fun e he =>
      (Real.continuousAt_const_rpow' (by linarith [he.1])).continuousWithinAt
    exact this.mul continuousOn_const

theorem s113b_mix {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {a c f : ℕ → α → ℝ}
    {a0 c0 f0 : α → ℝ} {C : ℝ}
    (ham : ∀ k, AEStronglyMeasurable (a k) μ) (hcm : ∀ k, AEStronglyMeasurable (c k) μ)
    (hab : ∀ k, ∀ᵐ x ∂μ, ‖a k x‖ ≤ C) (hcb : ∀ k, ∀ᵐ x ∂μ, ‖c k x‖ ≤ C)
    (hal : ∀ᵐ x ∂μ, Tendsto (fun k => a k x) atTop (𝓝 (a0 x)))
    (hcl : ∀ᵐ x ∂μ, Tendsto (fun k => c k x) atTop (𝓝 (c0 x)))
    (hf0 : Integrable f0 μ) (hf : ∀ k, Integrable (f k) μ)
    (hL1 : Tendsto (fun k => ∫ x, ‖f k x - f0 x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, (a k x + f k x * c k x) ∂μ) atTop (𝓝 (∫ x, (a0 x + f0 x * c0 x) ∂μ)) := by
  have hae : ∀ {g : ℕ → α → ℝ} {g0 : α → ℝ}, (∀ k, AEStronglyMeasurable (g k) μ) →
      (∀ k, ∀ᵐ x ∂μ, ‖g k x‖ ≤ C) → (∀ᵐ x ∂μ, Tendsto (fun k => g k x) atTop (𝓝 (g0 x))) →
      AEStronglyMeasurable g0 μ ∧ ∀ᵐ x ∂μ, ‖g0 x‖ ≤ C := fun hm hb hl =>
    ⟨aestronglyMeasurable_of_tendsto_ae atTop hm hl, by
      filter_upwards [ae_all_iff.2 hb, hl] with x h1 h2
      exact le_of_tendsto' h2.norm h1⟩
  obtain ⟨ha0m, ha0b⟩ := hae ham hab hal
  obtain ⟨hc0m, hc0b⟩ := hae hcm hcb hcl
  have hfc : ∀ {g h : α → ℝ}, Integrable g μ → AEStronglyMeasurable h μ → (∀ᵐ x ∂μ, ‖h x‖ ≤ C) →
      Integrable (fun x => g x * h x) μ := fun hg hh hb =>
    (hg.norm.mul_const C).mono' (hg.1.mul hh) (hb.mono fun x hx => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hint : ∀ {g : α → ℝ}, AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, ‖g x‖ ≤ C) → Integrable g μ :=
    fun hg hb => Integrable.of_bound hg C hb
  have h1 : Tendsto (fun k => ∫ x, a k x ∂μ) atTop (𝓝 (∫ x, a0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C) ham (integrable_const C) hab hal
  have h2 : Tendsto (fun k => ∫ x, f0 x * c k x ∂μ) atTop (𝓝 (∫ x, f0 x * c0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖f0 x‖ * C) (fun k => hf0.1.mul (hcm k))
      (hf0.norm.mul_const C) (fun k => (hcb k).mono fun x hx => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      (hcl.mono fun x hx => hx.const_mul _)
  have h3 : Tendsto (fun k => ∫ x, (f k x - f0 x) * c k x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => (∫ x, ‖f k x - f0 x‖ ∂μ) * C) (fun k => ?_) (by simpa using hL1.mul_const C)
    rw [← MeasureTheory.integral_mul_const]
    exact norm_integral_le_of_norm_le (((hf k).sub hf0).norm.mul_const C) ((hcb k).mono fun x hx => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have := h1.add (h3.add h2)
  rw [zero_add, ← integral_add (hint ha0m ha0b) (hfc hf0 hc0m hc0b)] at this
  refine this.congr fun k => ?_
  have hi1 := hint (ham k) (hab k)
  have hi2 : Integrable (fun x => (f k x - f0 x) * c k x) μ := hfc ((hf k).sub hf0) (hcm k) (hcb k)
  have hi3 := hfc hf0 (hcm k) (hcb k)
  have hi4 : Integrable (fun x => (f k x - f0 x) * c k x + f0 x * c k x) μ := hi2.add hi3
  rw [← integral_add hi2 hi3, ← integral_add hi1 hi4]
  congr 1; ext x; ring


theorem s113b_approx {p : ℝ → ℝ} {T δ : ℝ} (hT : 0 ≤ T) (hp : AbsolutelyContinuousOnInterval p 0 T) (hδ : 0 < δ) :
    ∃ ψ : ℕ → ℝ → ℝ, (∀ k, Continuous (ψ k)) ∧
      ∀ k, ∫ x in (0:ℝ)..T, |ψ k x - deriv p x| ≤ δ * (1 / ((k : ℝ) + 1)) := by
  have hi : Integrable (deriv p) (volume.restrict (Icc 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hp.intervalIntegrable_deriv
  have : ∀ k : ℕ, ∃ g : ℝ → ℝ, (∫ x, ‖deriv p x - g x‖ ∂(volume.restrict (Icc 0 T))) ≤ δ * (1 / ((k : ℝ) + 1)) ∧
      Continuous g := fun k => by
    obtain ⟨g, -, h1, h2, -⟩ := hi.exists_hasCompactSupport_integral_sub_le (ε := δ * (1 / ((k : ℝ) + 1))) (by positivity)
    exact ⟨g, h1, h2⟩
  choose g hg hgc using this
  refine ⟨g, hgc, fun k => ?_⟩
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  simpa [Real.norm_eq_abs, abs_sub_comm] using hg k

/-- The `C¹` approximation `p_k(t) = p 0 + ∫_0^t ψ_k`. -/
def s113b_pk (p0 : ℝ) (ψ : ℝ → ℝ) (t : ℝ) : ℝ := p0 + ∫ x in (0:ℝ)..t, ψ x

theorem s113b_pk_deriv {ψ : ℝ → ℝ} (hψ : Continuous ψ) (p0 t : ℝ) : HasDerivAt (s113b_pk p0 ψ) (ψ t) t :=
  (hψ.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add p0

theorem s113b_pk_contDiff {ψ : ℝ → ℝ} (hψ : Continuous ψ) (p0 : ℝ) : ContDiff ℝ 1 (s113b_pk p0 ψ) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t => (s113b_pk_deriv hψ p0 t).differentiableAt, ?_⟩
  have : deriv (s113b_pk p0 ψ) = ψ := funext fun t => (s113b_pk_deriv hψ p0 t).deriv
  rwa [this]

theorem s113b_pk_err {p ψ : ℝ → ℝ} {T t : ℝ} (hp : AbsolutelyContinuousOnInterval p 0 T) (hψ : Continuous ψ)
    (ht : t ∈ Icc 0 T) : |s113b_pk (p 0) ψ t - p t| ≤ ∫ x in (0:ℝ)..T, |ψ x - deriv p x| := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hpt : AbsolutelyContinuousOnInterval p 0 t :=
    hp.mono (by rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2)
  have hI : IntervalIntegrable (fun x => ψ x - deriv p x) volume 0 T :=
    (hψ.intervalIntegrable 0 T).sub hp.intervalIntegrable_deriv
  have h1 : s113b_pk (p 0) ψ t - p t = ∫ x in (0:ℝ)..t, (ψ x - deriv p x) := by
    rw [intervalIntegral.integral_sub (hψ.intervalIntegrable 0 t) hpt.intervalIntegrable_deriv,
      hpt.integral_deriv_eq_sub, s113b_pk]; ring
  rw [h1]
  refine (abs_integral_le_integral_abs ht.1).trans (integral_mono_interval le_rfl ht.1 ht.2 ?_ hI.abs)
  exact ae_of_all _ fun x => abs_nonneg _

theorem s113b_Gp_eq {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    (P : ℝ → ℝ) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    s113b_Gp ν b q u P τ = (P τ - 1) * (∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (P τ)) +
      deriv P τ * ∫ x, q τ x * ((u τ x / q τ x) ^ (P τ) * Real.log (u τ x / q τ x)) := by
  have h1 : ∫ x, q τ x * s113b_R ν b q τ x * (u τ x / q τ x) ^ (P τ) =
      ∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (P τ) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show q τ x * (s113b_N ν b q τ x / q τ x) * _ = _
    rw [mul_div_cancel₀ _ (hD.hq0 τ hτ x).ne']
  unfold s113b_Gp
  rw [h1]
  simp only [mul_assoc]


theorem s113b_chain_ac {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    {p : ℝ → ℝ} (hp : AbsolutelyContinuousOnInterval p 0 T) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    s113b_M q u p t - s113b_M q u p s ≤ ∫ τ in s..t, s113b_Gp ν b q u p τ := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hpc : ContinuousOn p (Icc 0 T) := by simpa [uIcc_of_le hT] using hp.continuousOn
  obtain ⟨i1, hi1m, hi1⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hpc
  obtain ⟨i2, hi2m, hi2⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT) hpc
  have h1 := hp1 i1 hi1m
  have h1' := hp1 i2 hi2m
  set δ : ℝ := min ((p i1 - 1) / 2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ (p i1 - 1) / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 := min_le_right _ _
  obtain ⟨ψ, hψc, hψ⟩ := s113b_approx hT hp hδ
  set pk : ℕ → ℝ → ℝ := fun k => s113b_pk (p 0) (ψ k) with hpkdef
  have hε : Tendsto (fun k : ℕ => δ * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hε1 : ∀ k : ℕ, δ * (1 / ((k : ℝ) + 1)) ≤ δ := fun k =>
    mul_le_of_le_one_right hδ.le ((div_le_one (by positivity)).2 (by linarith [k.cast_nonneg (α := ℝ)]))
  have hpk : ∀ k, ∀ t ∈ Icc 0 T, |pk k t - p t| ≤ δ * (1 / ((k : ℝ) + 1)) := fun k t ht =>
    (s113b_pk_err hp (hψc k) ht).trans (hψ k)
  have hmem : ∀ k, ∀ t ∈ Icc 0 T, pk k t ∈ Icc ((1 + p i1) / 2) (p i2 + 1) := by
    intro k t ht
    have h2 := abs_le.1 (hpk k t ht)
    have h3 := hε1 k
    have h4 : p i1 ≤ p t := isMinOn_iff.1 hi1 t ht
    have h5 : p t ≤ p i2 := isMaxOn_iff.1 hi2 t ht
    constructor <;> linarith [h2.1, h2.2, hδ1, hδ2]
  have hptm : ∀ t ∈ Icc 0 T, p t ∈ Icc ((1 + p i1) / 2) (p i2 + 1) := fun t ht =>
    ⟨by linarith [(isMinOn_iff.1 hi1 t ht : p i1 ≤ p t)], by linarith [(isMaxOn_iff.1 hi2 t ht : p t ≤ p i2)]⟩
  have hcont : ∀ k, Continuous (pk k) := fun k => (s113b_pk_contDiff (hψc k) (p 0)).continuous
  have hder : ∀ k τ, deriv (pk k) τ = ψ k τ := fun k τ => (s113b_pk_deriv (hψc k) (p 0) τ).deriv
  have htend : ∀ t ∈ Icc 0 T, Tendsto (fun k => pk k t) atTop (𝓝[Icc ((1 + p i1) / 2) (p i2 + 1)] (p t)) :=
    fun t ht => tendsto_nhdsWithin_iff.2 ⟨tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _)
      (fun k => by simpa [Real.norm_eq_abs] using hpk k t ht) hε), Eventually.of_forall fun k => hmem k t ht⟩
  have htend' : ∀ t ∈ Icc 0 T, Tendsto (fun k => pk k t) atTop (𝓝 (p t)) := fun t ht => (htend t ht).mono_right nhdsWithin_le_nhds
  obtain ⟨Z, hZ0, hr⟩ := s113b_ratio hD
  have ha0 : 0 < (1 + p i1) / 2 := by linarith
  have hφ1 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1) := measurable_snd.pow measurable_fst
  have hφ2 : Measurable (fun y : ℝ × ℝ => y.2 ^ y.1 * Real.log y.2) := hφ1.mul (Real.measurable_log.comp measurable_snd)
  have famQ := s113b_fam hD (w := q) hD.hq.continuous (φ := fun e z => z ^ e) hr hφ1 (s113b_pow_props _ (p i2 + 1) Z ha0 hZ0)
  have famN := s113b_fam hD (w := s113b_N ν b q) (s113b_N_contB9 ν hD.hb hD.hq) (φ := fun e z => z ^ e) hr hφ1
    (s113b_pow_props _ (p i2 + 1) Z ha0 hZ0)
  have famC := s113b_fam hD (w := q) hD.hq.continuous (φ := fun e z => z ^ e * Real.log z) hr hφ2
    (s113b_log_props _ (p i2 + 1) Z ha0 hZ0)
  obtain ⟨CA, hCA⟩ := famN.2.1
  obtain ⟨CC, hCC⟩ := famC.2.1
  -- limits of the masses
  have hM : ∀ t ∈ Icc 0 T, Tendsto (fun k => s113b_M q u (pk k) t) atTop (𝓝 (s113b_M q u p t)) :=
    fun t ht => ((famQ.1 t ht).continuousWithinAt (hptm t ht)).tendsto.comp (htend t ht)
  -- limit of the integrals
  have hS : ∀ τ ∈ Ioc s t, τ ∈ Icc 0 T := fun τ hτ => ⟨hs.trans hτ.1.le, hτ.2.trans htT⟩
  have hint0 : IntegrableOn (deriv p) (Ioc s t) := (hp.mono (by
    rw [uIcc_of_le hst, uIcc_of_le hT]; exact Icc_subset_Icc hs htT)).intervalIntegrable_deriv.1
  have hR : Tendsto (fun k => ∫ τ in s..t, s113b_Gp ν b q u (pk k) τ) atTop (𝓝 (∫ τ in s..t, s113b_Gp ν b q u p τ)) := by
    simp only [intervalIntegral.integral_of_le hst]
    have e1 : ∀ P : ℕ → ℝ → ℝ, ∀ k, ∫ τ in Ioc s t, s113b_Gp ν b q u (P k) τ = ∫ τ in Ioc s t,
        ((P k τ - 1) * (∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (P k τ)) +
          deriv (P k) τ * ∫ x, q τ x * ((u τ x / q τ x) ^ (P k τ) * Real.log (u τ x / q τ x))) :=
      fun P k => setIntegral_congr_fun measurableSet_Ioc fun τ hτ => s113b_Gp_eq hD (P k) (hS τ hτ)
    have e2 : ∫ τ in Ioc s t, s113b_Gp ν b q u p τ = ∫ τ in Ioc s t,
        ((p τ - 1) * (∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (p τ)) +
          deriv p τ * ∫ x, q τ x * ((u τ x / q τ x) ^ (p τ) * Real.log (u τ x / q τ x))) :=
      setIntegral_congr_fun measurableSet_Ioc fun τ hτ => s113b_Gp_eq hD p (hS τ hτ)
    rw [e2]
    have hae : ∀ {P : ℝ → Prop}, (∀ τ ∈ Ioc s t, P τ) → ∀ᵐ τ ∂(volume.restrict (Ioc s t)), P τ := fun h =>
      (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ h)
    refine Tendsto.congr (fun k => ?_) (s113b_mix (a0 := fun τ => (p τ - 1) * ∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (p τ)) (c0 := fun τ => ∫ x, q τ x * ((u τ x / q τ x) ^ (p τ) * Real.log (u τ x / q τ x))) (f0 := deriv p) (C := max (CA * (p i2 + 1)) CC) (a := fun k τ => (pk k τ - 1) * ∫ x, s113b_N ν b q τ x * (u τ x / q τ x) ^ (pk k τ))
      (c := fun k τ => ∫ x, q τ x * ((u τ x / q τ x) ^ (pk k τ) * Real.log (u τ x / q τ x))) (f := ψ) ?_ ?_ ?_ ?_ ?_ ?_ hint0 ?_ ?_)
    · rw [e1 pk k]; simp only [hder]
    · exact fun k => (((hcont k).sub continuous_const).aestronglyMeasurable.mul (famN.2.2 _ (hcont k))).restrict
    · exact fun k => ((famC.2.2 _ (hcont k))).restrict
    · refine fun k => hae fun τ hτ => ?_
      have hm := hmem k τ (hS τ hτ)
      have h0 : |pk k τ - 1| ≤ p i2 + 1 := by
        rw [abs_of_nonneg (by linarith [hm.1])]; linarith [hm.2]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm CA]
      exact (mul_le_mul h0 (hCA τ (hS τ hτ) _ hm) (abs_nonneg _) (by linarith)).trans (le_max_left _ _)
    · exact fun k => hae fun τ hτ => (hCC τ (hS τ hτ) _ (hmem k τ (hS τ hτ))).trans (le_max_right _ _)
    · exact hae fun τ hτ => ((htend' τ (hS τ hτ)).sub_const 1).mul (((famN.1 τ (hS τ hτ)).continuousWithinAt (hptm τ (hS τ hτ))).tendsto.comp (htend τ (hS τ hτ)))
    · exact hae fun τ hτ => ((famC.1 τ (hS τ hτ)).continuousWithinAt (hptm τ (hS τ hτ))).tendsto.comp (htend τ (hS τ hτ))
    · exact fun k => (hψc k).integrableOn_Ioc
    · simp only [Real.norm_eq_abs]
      refine squeeze_zero (fun k => integral_nonneg fun x => abs_nonneg _) (fun k => ?_) hε
      have hI : IntervalIntegrable (fun x => |ψ k x - deriv p x|) volume 0 T :=
        (((hψc k).intervalIntegrable 0 T).sub hp.intervalIntegrable_deriv).abs
      refine le_trans ?_ (hψ k)
      rw [intervalIntegral.integral_of_le hT]
      exact setIntegral_mono_set hI.1 (ae_of_all _ fun x => abs_nonneg _) (Ioc_subset_Ioc hs htT).eventuallyLE
  exact le_of_tendsto_of_tendsto ((hM t ⟨hs.trans hst, htT⟩).sub (hM s ⟨hs, hst.trans htT⟩)) hR
    (Eventually.of_forall fun k => s113b_chain_C1 hD (s113b_pk_contDiff (hψc k) (p 0))
      (fun t ht => by linarith [(hmem k t ht).1]) hs hst htT)

end HRS.MS.S113X2B
