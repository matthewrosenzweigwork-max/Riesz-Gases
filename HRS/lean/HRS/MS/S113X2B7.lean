import HRS.MS.S113X2B3L
import HRS.MS.S113X2B6

/-! # S11.3 X2 part B, B7: the epsilon-level chain inequality

Passing `δ → 0+` in the mollified chain inequality at fixed `ε`, by dominated convergence (in `x`, then in `τ`),
organised through the predicate `s113b_Good` (measurable, uniformly bounded, supported in `K'`, a.e. convergent). -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.S113X2B

section Aux

variable {n : ℕ}

/-- Partial derivative of a differentiable function of `(τ, y)` in the direction `(0, w)`. -/
lemma s113b_part {Ψ : ℝ × s113b_E n → ℝ} (hΨ : Differentiable ℝ Ψ) (τ : ℝ) (x w : s113b_E n) :
    fderiv ℝ (fun y => Ψ (τ, y)) x w = fderiv ℝ Ψ (τ, x) (0, w) := by
  have h := (hΨ (τ, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right τ x)
  rw [show (fun y => Ψ (τ, y)) = Ψ ∘ fun y => (τ, y) from rfl, h.fderiv]
  simp

/-- The numerator `q R` of the source is jointly continuous. -/
lemma s113b_N_cont {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} (hb : ContDiff ℝ 2 b)
    (hq : ContDiff ℝ 2 (fun z : ℝ × s113b_E n => q z.1 z.2)) :
    Continuous (fun z : ℝ × s113b_E n => ν * s113b_lap (q z.1) z.2 -
      s113b_div (fun y => q z.1 y • b y) z.2 - deriv (fun σ => q σ z.2) z.1) := by
  set Q : ℝ × s113b_E n → ℝ := fun z => q z.1 z.2 with hQ
  have hQd : Differentiable ℝ Q := hq.differentiable (by norm_num)
  let e : Fin n → s113b_E n := fun k => EuclideanSpace.single k 1
  let Z : Fin n → ℝ × s113b_E n → ℝ := fun k z => fderiv ℝ Q z (0, e k)
  let Y : Fin n → ℝ × s113b_E n → ℝ := fun k z => Q z * b z.2 k
  have hZ : ∀ k, ContDiff ℝ 1 (Z k) := fun k =>
    (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hY : ∀ k, ContDiff ℝ 1 (Y k) := fun k =>
    (hq.of_le (by norm_num)).mul ((s113b_coord_cd (hb.of_le (by norm_num)) k).comp contDiff_snd)
  have hqτ : ∀ τ, ContDiff ℝ 2 (q τ) := fun τ => hq.comp (contDiff_const.prodMk contDiff_id)
  have hfd : ∀ τ y w, fderiv ℝ (q τ) y w = fderiv ℝ Q (τ, y) (0, w) := fun τ y w => s113b_part hQd τ y w
  have key : ∀ z : ℝ × s113b_E n, ν * s113b_lap (q z.1) z.2 - s113b_div (fun y => q z.1 y • b y) z.2 -
      deriv (fun σ => q σ z.2) z.1 =
      ν * ∑ k, fderiv ℝ (Z k) z (0, e k) - ∑ k, fderiv ℝ (Y k) z (0, e k) - fderiv ℝ Q z (1, 0) := by
    rintro ⟨τ, x⟩
    have h1 : s113b_lap (q τ) x = ∑ k, fderiv ℝ (Z k) (τ, x) (0, e k) := by
      rw [s113b_lap_eq (hqτ τ)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (fun y => fderiv ℝ (q τ) y (e k)) = fun y => Z k (τ, y) := funext fun y => hfd τ y _
      rw [this, s113b_part ((hZ k).differentiable (by norm_num)) τ x]
    have h2 : s113b_div (fun y => q τ y • b y) x = ∑ k, fderiv ℝ (Y k) (τ, x) (0, e k) := by
      rw [s113b_div_smul]
      exact Finset.sum_congr rfl fun k _ => s113b_part ((hY k).differentiable (by norm_num)) τ x _
    have h3 : deriv (fun σ => q σ x) τ = fderiv ℝ Q (τ, x) (1, 0) := by
      have hf : HasDerivAt (fun σ : ℝ => (σ, x)) ((1 : ℝ), (0 : s113b_E n)) τ :=
        (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ x)
      exact ((hQd (τ, x)).hasFDerivAt.comp_hasDerivAt τ hf).deriv
    show ν * s113b_lap (q τ) x - s113b_div (fun y => q τ y • b y) x - deriv (fun σ => q σ x) τ = _
    rw [h1, h2, h3]
  rw [show (fun z : ℝ × s113b_E n => ν * s113b_lap (q z.1) z.2 - s113b_div (fun y => q z.1 y • b y) z.2 -
      deriv (fun σ => q σ z.2) z.1) = _ from funext key]
  refine ((continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)).sub
    (continuous_finsetSum _ fun k _ => ?_)).sub ?_
  · exact ((hZ k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact ((hY k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  · exact (hq.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Joint measurability of the commutator. -/
lemma s113b_comm_measurable (m : s113b_Moll n) (δ : ℝ) {b : s113b_E n → s113b_E n} (hb : Continuous b)
    {U : ℝ × s113b_E n → ℝ} (hU : Measurable U) :
    Measurable fun z : ℝ × s113b_E n => s113b_comm m δ b (fun y => U (z.1, y)) z.2 := by
  have hD : Continuous (fderiv ℝ (m.scaled δ)) := (s113b_scaled_c1 m δ).continuous_fderiv (by norm_num)
  have hdiv : Measurable (s113b_div b) :=
    Finset.measurable_sum _ fun k _ => measurable_fderiv_apply_const ℝ _ _
  have hρ := (s113b_scaled_cinf m δ).continuous
  have c1 : Continuous fun p : (ℝ × s113b_E n) × s113b_E n => p.1.2 - p.2 :=
    (continuous_snd.comp continuous_fst).sub continuous_snd
  have c2 : Continuous fun p : (ℝ × s113b_E n) × s113b_E n => p.1.2 := continuous_snd.comp continuous_fst
  have hc : Continuous fun p : (ℝ × s113b_E n) × s113b_E n =>
      fderiv ℝ (m.scaled δ) (p.1.2 - p.2) (b p.1.2 - b p.2) :=
    (hD.comp c1).clm_apply ((hb.comp c2).sub (hb.comp continuous_snd))
  have hH : Measurable fun p : (ℝ × s113b_E n) × s113b_E n => U (p.1.1, p.2) *
      (fderiv ℝ (m.scaled δ) (p.1.2 - p.2) (b p.1.2 - b p.2) + s113b_div b p.1.2 * m.scaled δ (p.1.2 - p.2)) :=
    (hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hc.measurable.add ((hdiv.comp c2.measurable).mul (hρ.measurable.comp c1.measurable)))
  exact (hH.stronglyMeasurable.integral_prod_right').measurable

/-- A family `f δ τ x` which is measurable, uniformly bounded and supported in `K'` for `τ ∈ [0,T]`, `δ ∈ (0,δ0]`,
and converges a.e. in `x` as `δ → 0+`. -/
def s113b_Good (T δ0 : ℝ) (K' : Set (s113b_E n)) (f : ℝ → ℝ → s113b_E n → ℝ) (f0 : ℝ → s113b_E n → ℝ) : Prop :=
  (∀ δ ∈ Ioc 0 δ0, Measurable fun z : ℝ × s113b_E n => f δ z.1 z.2) ∧
  (∃ C, ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, |f δ τ x| ≤ C ∧ (x ∉ K' → f δ τ x = 0)) ∧
  (∀ τ ∈ Icc 0 T, ∀ᵐ x ∂(volume : Measure (s113b_E n)),
    Tendsto (fun δ => f δ τ x) (𝓝[>] 0) (𝓝 (f0 τ x)))

lemma s113b_good_add {T δ0 : ℝ} {K' : Set (s113b_E n)} {f g : ℝ → ℝ → s113b_E n → ℝ}
    {f0 g0 : ℝ → s113b_E n → ℝ} (hf : s113b_Good T δ0 K' f f0) (hg : s113b_Good T δ0 K' g g0) :
    s113b_Good T δ0 K' (fun δ τ x => f δ τ x + g δ τ x) (fun τ x => f0 τ x + g0 τ x) := by
  obtain ⟨m1, ⟨C1, b1⟩, l1⟩ := hf
  obtain ⟨m2, ⟨C2, b2⟩, l2⟩ := hg
  refine ⟨fun δ hδ => (m1 δ hδ).add (m2 δ hδ), ⟨C1 + C2, fun δ hδ τ hτ x => ⟨?_, fun hx => ?_⟩⟩,
    fun τ hτ => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (b1 δ hδ τ hτ x).1 (b2 δ hδ τ hτ x).1)
  · simp [(b1 δ hδ τ hτ x).2 hx, (b2 δ hδ τ hτ x).2 hx]
  · filter_upwards [l1 τ hτ, l2 τ hτ] with x h1 h2 using h1.add h2

lemma s113b_good_congr {T δ0 : ℝ} {K' : Set (s113b_E n)} {f g : ℝ → ℝ → s113b_E n → ℝ}
    {f0 g0 : ℝ → s113b_E n → ℝ} (h : s113b_Good T δ0 K' f f0) (hf : ∀ δ τ x, f δ τ x = g δ τ x)
    (hf0 : ∀ τ x, f0 τ x = g0 τ x) : s113b_Good T δ0 K' g g0 := by
  obtain rfl : f = g := funext fun δ => funext fun τ => funext fun x => hf δ τ x
  obtain rfl : f0 = g0 := funext fun τ => funext fun x => hf0 τ x
  exact h

/-- Dominated convergence in `x`; bound and measurability in `τ` of the resulting integrals. -/
lemma s113b_good_int {T δ0 : ℝ} {K' : Set (s113b_E n)} {f : ℝ → ℝ → s113b_E n → ℝ}
    {f0 : ℝ → s113b_E n → ℝ} (hK : IsCompact K') (hδ0 : 0 < δ0) (h : s113b_Good T δ0 K' f f0) :
    (∀ τ ∈ Icc 0 T, Tendsto (fun δ => ∫ x, f δ τ x) (𝓝[>] 0) (𝓝 (∫ x, f0 τ x))) ∧
    (∃ C, ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, |∫ x, f δ τ x| ≤ C) ∧
    (∀ δ ∈ Ioc 0 δ0, Measurable fun τ => ∫ x, f δ τ x) := by
  obtain ⟨hm, ⟨C, hb⟩, hl⟩ := h
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioc 0 δ0 := Ioc_mem_nhdsGT hδ0
  have hint : Integrable (K'.indicator fun _ => C) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbd : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, ‖f δ τ x‖ ≤ K'.indicator (fun _ => C) x := by
    intro δ hδ τ hτ x
    by_cases hx : x ∈ K'
    · simpa [hx] using (hb δ hδ τ hτ x).1
    · simp [hx, (hb δ hδ τ hτ x).2 hx]
  refine ⟨fun τ hτ => ?_, ⟨∫ x, K'.indicator (fun _ => C) x, fun δ hδ τ hτ => ?_⟩, fun δ hδ => ?_⟩
  · exact tendsto_integral_filter_of_dominated_convergence _
      (hev.mono fun δ hδ => ((hm δ hδ).comp measurable_prodMk_left).aestronglyMeasurable)
      (hev.mono fun δ hδ => ae_of_all _ (hbd δ hδ τ hτ)) hint (hl τ hτ)
  · simpa using norm_integral_le_of_norm_le hint (ae_of_all _ (hbd δ hδ τ hτ))
  · exact ((hm δ hδ).stronglyMeasurable.integral_prod_right').measurable

/-- The basic building block `c · G(p, ε, r_δ) · w_δ`. -/
lemma s113b_good_prod {T δ0 ε p1 p2 Z Cc Cw : ℝ} {K' : Set (s113b_E n)} {G : ℝ → ℝ → ℝ → ℝ} {p : ℝ → ℝ}
    {r w : ℝ → ℝ → s113b_E n → ℝ} {r0 w0 c : ℝ → s113b_E n → ℝ} (hδ0 : 0 < δ0)
    (hGm : Measurable fun y : ℝ × ℝ => G y.1 ε y.2)
    (hGc : ContinuousOn (fun y : ℝ × ℝ => G y.1 ε y.2) (Ioi 0 ×ˢ Ici 0)) (hG0 : ∀ a, G a ε 0 = 0)
    (hpm : Measurable p) (hp1 : 0 < p1) (hp : ∀ τ ∈ Icc 0 T, p τ ∈ Icc p1 p2)
    (hcm : Measurable fun z : ℝ × s113b_E n => c z.1 z.2) (hcb : ∀ τ ∈ Icc 0 T, ∀ x ∈ K', |c τ x| ≤ Cc)
    (hrm : ∀ δ ∈ Ioc 0 δ0, Measurable fun z : ℝ × s113b_E n => r δ z.1 z.2)
    (hrr : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, r δ τ x ∈ Icc 0 Z)
    (hrs : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, x ∉ K' → r δ τ x = 0)
    (hr0 : ∀ τ ∈ Icc 0 T, ∀ x, 0 ≤ r0 τ x)
    (hrl : ∀ τ ∈ Icc 0 T, ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ => r δ τ x) (𝓝[>] 0) (𝓝 (r0 τ x)))
    (hwm : ∀ δ ∈ Ioc 0 δ0, Measurable fun z : ℝ × s113b_E n => w δ z.1 z.2)
    (hwb : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, |w δ τ x| ≤ Cw)
    (hwl : ∀ τ ∈ Icc 0 T, ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ => w δ τ x) (𝓝[>] 0) (𝓝 (w0 τ x))) :
    s113b_Good T δ0 K' (fun δ τ x => c τ x * G (p τ) ε (r δ τ x) * w δ τ x)
      (fun τ x => c τ x * G (p τ) ε (r0 τ x) * w0 τ x) := by
  have hsub : Icc p1 p2 ×ˢ Icc 0 Z ⊆ Ioi 0 ×ˢ Ici 0 :=
    prod_mono (fun a ha => lt_of_lt_of_le hp1 ha.1) Icc_subset_Ici_self
  obtain ⟨CG, hCG⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (hGc.mono hsub)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioc 0 δ0 := Ioc_mem_nhdsGT hδ0
  refine ⟨fun δ hδ => (hcm.mul (hGm.comp ((hpm.comp measurable_fst).prodMk (hrm δ hδ)))).mul (hwm δ hδ),
    ⟨|Cc| * |CG| * |Cw|, fun δ hδ τ hτ x => ⟨?_, fun hx => ?_⟩⟩, fun τ hτ => ?_⟩
  · show |c τ x * G (p τ) ε (r δ τ x) * w δ τ x| ≤ _
    by_cases hx : x ∈ K'
    · have h2 : |G (p τ) ε (r δ τ x)| ≤ CG := by
        simpa only [Real.norm_eq_abs] using hCG (p τ, r δ τ x) ⟨hp τ hτ, hrr δ hδ τ hτ x⟩
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul ((hcb τ hτ x hx).trans (le_abs_self _)) (h2.trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)) ((hwb δ hδ τ hτ x).trans (le_abs_self _)) (abs_nonneg _)
        (by positivity)
    · rw [hrs δ hδ τ hτ x hx, hG0, mul_zero, zero_mul, abs_zero]; positivity
  · simp [hrs δ hδ τ hτ x hx, hG0]
  · filter_upwards [hrl τ hτ, hwl τ hτ] with x hr hw
    have hp0 : 0 < p τ := lt_of_lt_of_le hp1 (hp τ hτ).1
    have hG : Tendsto (fun δ => G (p τ) ε (r δ τ x)) (𝓝[>] 0) (𝓝 (G (p τ) ε (r0 τ x))) :=
      (hGc.continuousWithinAt (show (p τ, r0 τ x) ∈ Ioi (0 : ℝ) ×ˢ Ici 0 from ⟨hp0, hr0 τ hτ x⟩)).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hr,
          hev.mono fun δ hδ => ⟨hp0, (hrr δ hδ τ hτ x).1⟩⟩)
    exact (tendsto_const_nhds.mul hG).mul hw

end Aux

theorem s113b_eps_chain {n : ℕ} {ν : ℝ} {b : s113b_E n → s113b_E n} {q : ℝ → s113b_E n → ℝ} {T : ℝ}
    {u : ℝ → s113b_E n → ℝ} {K G : Set (s113b_E n)} {B : ℝ} (hD : s113b_Data ν b q T u K G B)
    {p : ℝ → ℝ} (hp : ContDiff ℝ 1 p) (hp1 : ∀ t ∈ Icc 0 T, 1 < p t) {ε : ℝ} (hε : 0 < ε)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    (∫ x, s113b_F q p ε t x (u t x)) - ∫ x, s113b_F q p ε s x (u s x) ≤
      ∫ τ in s..t, s113b_rhsE ν b q p ε τ (fun x => u τ x / q τ x) := by
  have hT0 : 0 ≤ T := hs.trans (hst.trans htT)
  obtain ⟨m⟩ := s113b_Moll_exists n
  obtain ⟨δ1, hδ1, hδ1G⟩ := hD.hKc.exists_cthickening_subset_open hD.hG hD.hKG
  obtain ⟨δc, Cc, hδc, hcomm⟩ := s113b_comm_bound m hD.hb hD.hKc
  have hδ0 : 0 < min (δ1 / 2) (δc / 2) := lt_min (by linarith) (by linarith)
  set δ0 := min (δ1 / 2) (δc / 2) with hδ0def
  have hδ0a : δ0 ≤ δ1 / 2 := min_le_left _ _
  have hδ0b : δ0 ≤ δc / 2 := min_le_right _ _
  set K' := Metric.cthickening δ0 K with hK'def
  have hK' : IsCompact K' := hD.hKc.cthickening
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioc 0 δ0 := Ioc_mem_nhdsGT hδ0
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.trans htT⟩
  have htI : t ∈ Icc 0 T := ⟨hs.trans hst, htT⟩
  -- facts on `u` and its mollification
  have hum : ∀ τ, Measurable (u τ) := fun τ => hD.hum.comp measurable_prodMk_left
  have huB : ∀ τ ∈ Icc 0 T, ∀ y, |u τ y| ≤ B := fun τ hτ y => by
    rw [abs_of_nonneg (hD.hu0 τ y)]; exact hD.huB τ hτ y
  have hB0 : 0 ≤ B := (hD.hu0 0 0).trans (hD.huB 0 ⟨le_rfl, hT0⟩ 0)
  have hv0 : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, 0 ≤ s113b_mol m δ (u τ) x := fun δ hδ τ hτ x =>
    s113b_mol_nonneg (hum τ) (huB τ hτ) hD.hKc (hD.hKu τ) m hδ.1 (hD.hu0 τ) x
  have hvB : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, s113b_mol m δ (u τ) x ≤ B := fun δ hδ τ hτ x =>
    s113b_mol_le (hum τ) (huB τ hτ) hD.hKc (hD.hKu τ) m hδ.1 (hD.huB τ hτ) x
  have hvK : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, x ∉ K' → s113b_mol m δ (u τ) x = 0 := by
    intro δ hδ τ hτ x hx
    refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
    exact Metric.cthickening_mono hδ.2 K (s113b_mol_tsupport (hum τ) (huB τ hτ) hD.hKc (hD.hKu τ) m hδ.1 h)
  -- bounds on `q`, `p`, `qR`, `p' q`
  have hQc : Continuous (fun z : ℝ × s113b_E n => q z.1 z.2) := hD.hq.continuous
  have hS : IsCompact (Icc 0 T ×ˢ K') := isCompact_Icc.prod hK'
  obtain ⟨Ci, hCi⟩ := hS.exists_bound_of_continuousOn (f := fun z : ℝ × s113b_E n => (q z.1 z.2)⁻¹)
    (fun z hz => ((hQc.continuousAt).inv₀ (hD.hq0 z.1 hz.1 z.2).ne').continuousWithinAt)
  obtain ⟨Cq, hCq⟩ := hS.exists_bound_of_continuousOn hQc.continuousOn
  have hN := s113b_N_cont (ν := ν) hD.hb hD.hq
  obtain ⟨CN, hCN⟩ := hS.exists_bound_of_continuousOn hN.continuousOn
  have hdp : Continuous (deriv p) := hp.continuous_deriv (by norm_num)
  obtain ⟨Cd, hCd⟩ := hS.exists_bound_of_continuousOn ((hdp.comp continuous_fst).mul hQc).continuousOn
  obtain ⟨a, haI, ha⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT0) hp.continuous.continuousOn
  obtain ⟨P, hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hp.continuous.continuousOn : ContinuousOn p (Icc 0 T))
  have hpr : ∀ τ ∈ Icc 0 T, p τ ∈ Icc (p a) P := fun τ hτ =>
    ⟨isMinOn_iff.1 ha τ hτ, (le_abs_self _).trans (by simpa using hP τ hτ)⟩
  have hpa : 0 < p a := lt_trans one_pos (hp1 a haI)
  have hqR : ∀ τ ∈ Icc 0 T, ∀ x, q τ x * s113b_R ν b q τ x = ν * s113b_lap (q τ) x -
      s113b_div (fun y => q τ y • b y) x - deriv (fun σ => q σ x) τ := by
    intro τ hτ x
    have := (hD.hq0 τ hτ x).ne'
    unfold s113b_R; field_simp
  -- the ratio family
  let rr : ℝ → ℝ → s113b_E n → ℝ := fun δ τ x => s113b_mol m δ (u τ) x / q τ x
  let r0 : ℝ → s113b_E n → ℝ := fun τ x => u τ x / q τ x
  have hrm : ∀ δ ∈ Ioc 0 δ0, Measurable fun z : ℝ × s113b_E n => rr δ z.1 z.2 := fun δ _ =>
    (s113b_mol_measurable m δ hD.hum).div hQc.measurable
  have hrr : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, rr δ τ x ∈ Icc 0 (B * max Ci 0) := by
    intro δ hδ τ hτ x
    refine ⟨div_nonneg (hv0 δ hδ τ hτ x) (hD.hq0 τ hτ x).le, ?_⟩
    by_cases hx : x ∈ K'
    · have h2 : (q τ x)⁻¹ ≤ max Ci 0 :=
        (le_abs_self _).trans ((by simpa using hCi (τ, x) ⟨hτ, hx⟩ : |(q τ x)⁻¹| ≤ Ci).trans (le_max_left _ _))
      exact mul_le_mul (hvB δ hδ τ hτ x) h2 (inv_nonneg.2 (hD.hq0 τ hτ x).le) hB0
    · show s113b_mol m δ (u τ) x / q τ x ≤ _
      rw [hvK δ hδ τ hτ x hx, zero_div]; exact mul_nonneg hB0 (le_max_right _ _)
  have hrs : ∀ δ ∈ Ioc 0 δ0, ∀ τ ∈ Icc 0 T, ∀ x, x ∉ K' → rr δ τ x = 0 := fun δ hδ τ hτ x hx => by
    show s113b_mol m δ (u τ) x / q τ x = 0
    rw [hvK δ hδ τ hτ x hx, zero_div]
  have hr0 : ∀ τ ∈ Icc 0 T, ∀ x, 0 ≤ r0 τ x := fun τ hτ x => div_nonneg (hD.hu0 τ x) (hD.hq0 τ hτ x).le
  have hrl : ∀ τ ∈ Icc 0 T, ∀ᵐ x ∂(volume : Measure (s113b_E n)),
      Tendsto (fun δ => rr δ τ x) (𝓝[>] 0) (𝓝 (r0 τ x)) := fun τ hτ => by
    filter_upwards [s113b_mol_tendsto_ae m (hum τ) (huB τ hτ) hD.hKc (hD.hKu τ)] with x hx using
      hx.div_const _
  -- profiles
  have hpm : Measurable p := hp.continuous.measurable
  have hΦ := s113b_continuousOn_Phi ε hε
  have hΦ1 := s113b_continuousOn_Phi1 ε hε
  have hΘ := s113b_continuousOn_Theta ε hε
  have hPP := s113b_continuousOn_PhiP ε hε
  have hΦm : Measurable fun y : ℝ × ℝ => s113b_Phi y.1 ε y.2 := by unfold s113b_Phi; fun_prop
  have hΦ1m : Measurable fun y : ℝ × ℝ => s113b_Phi1 y.1 ε y.2 := by unfold s113b_Phi1; fun_prop
  have hΘm : Measurable fun y : ℝ × ℝ => s113b_Theta y.1 ε y.2 := by
    unfold s113b_Theta s113b_Phi1 s113b_Phi; fun_prop
  have hPPm : Measurable fun y : ℝ × ℝ => s113b_PhiP y.1 ε y.2 := by unfold s113b_PhiP; fun_prop
  have hPP0 : ∀ a, s113b_PhiP a ε 0 = 0 := fun a => by simp [s113b_PhiP]
  -- the three Good families
  have gA : s113b_Good T δ0 K' (fun δ τ x => s113b_F q p ε τ x (s113b_mol m δ (u τ) x))
      (fun τ x => s113b_F q p ε τ x (u τ x)) := by
    refine s113b_good_congr (s113b_good_prod (K' := K') (r := rr) (r0 := r0) (c := fun τ x => q τ x)
      (w := fun _ _ _ => (1 : ℝ)) (w0 := fun _ _ => (1 : ℝ)) (Cc := Cq) (Cw := 1) (Z := B * max Ci 0)
      hδ0 hΦm hΦ (fun a => s113b_Phi_zero a ε) hpm hpa hpr hQc.measurable
      (fun τ hτ x hx => by simpa using hCq (τ, x) ⟨hτ, hx⟩) hrm hrr hrs hr0 hrl
      (fun _ _ => measurable_const) (fun _ _ _ _ _ => by simp)
      (fun _ _ => ae_of_all _ fun _ => tendsto_const_nhds)) ?_ ?_ <;> intros <;> simp [s113b_F, rr, r0]
  have gB : s113b_Good T δ0 K' (fun δ τ x => q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (rr δ τ x) +
      deriv p τ * q τ x * s113b_PhiP (p τ) ε (rr δ τ x))
      (fun τ x => q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (r0 τ x) +
      deriv p τ * q τ x * s113b_PhiP (p τ) ε (r0 τ x)) := by
    have hc1 : Measurable fun z : ℝ × s113b_E n => q z.1 z.2 * s113b_R ν b q z.1 z.2 :=
      hQc.measurable.mul (hN.measurable.div hQc.measurable)
    refine s113b_good_congr (s113b_good_add
      (s113b_good_prod (K' := K') (r := rr) (r0 := r0) (c := fun τ x => q τ x * s113b_R ν b q τ x)
        (w := fun _ _ _ => (1 : ℝ)) (w0 := fun _ _ => (1 : ℝ)) (Cc := CN) (Cw := 1) (Z := B * max Ci 0)
        hδ0 hΘm hΘ (fun a => s113b_Theta_zero a ε) hpm hpa hpr hc1
        (fun τ hτ x hx => by rw [hqR τ hτ x]; simpa using hCN (τ, x) ⟨hτ, hx⟩) hrm hrr hrs hr0 hrl
        (fun _ _ => measurable_const) (fun _ _ _ _ _ => by simp)
        (fun _ _ => ae_of_all _ fun _ => tendsto_const_nhds))
      (s113b_good_prod (K' := K') (r := rr) (r0 := r0) (c := fun τ x => deriv p τ * q τ x)
        (w := fun _ _ _ => (1 : ℝ)) (w0 := fun _ _ => (1 : ℝ)) (Cc := Cd) (Cw := 1) (Z := B * max Ci 0)
        hδ0 hPPm hPP hPP0 hpm hpa hpr ((hdp.measurable.comp measurable_fst).mul hQc.measurable)
        (fun τ hτ x hx => by simpa using hCd (τ, x) ⟨hτ, hx⟩) hrm hrr hrs hr0 hrl
        (fun _ _ => measurable_const) (fun _ _ _ _ _ => by simp)
        (fun _ _ => ae_of_all _ fun _ => tendsto_const_nhds))) ?_ ?_ <;> intros <;> simp
  have gC : s113b_Good T δ0 K' (fun δ τ x => s113b_Phi1 (p τ) ε (rr δ τ x) * s113b_comm m δ b (u τ) x)
      (fun τ x => 0) := by
    refine s113b_good_congr (s113b_good_prod (K' := K') (r := rr) (r0 := r0) (c := fun _ _ => (1 : ℝ))
      (w := fun δ τ x => s113b_comm m δ b (u τ) x) (w0 := fun _ _ => (0 : ℝ)) (Cc := 1) (Cw := Cc * B)
      (Z := B * max Ci 0) hδ0 hΦ1m hΦ1 (fun a => s113b_Phi1_zero a ε) hpm hpa hpr measurable_const
      (fun _ _ _ _ => by simp) hrm hrr hrs hr0 hrl
      (fun δ _ => s113b_comm_measurable m δ hD.hb.continuous hD.hum)
      (fun δ hδ τ hτ x => hcomm B (u τ) (hum τ) (huB τ hτ) (hD.hKu τ) δ
        ⟨hδ.1, lt_of_le_of_lt hδ.2 (by linarith)⟩ x)
      (fun τ hτ => s113b_comm_tendsto_ae m hD.hb (hum τ) (huB τ hτ) hD.hKc (hD.hKu τ))) ?_ ?_ <;>
      intros <;> simp
  obtain ⟨tA, -, -⟩ := s113b_good_int hK' hδ0 gA
  obtain ⟨tB, ⟨CB, bB⟩, mB⟩ := s113b_good_int hK' hδ0 gB
  obtain ⟨tC, ⟨CC, bC⟩, mC⟩ := s113b_good_int hK' hδ0 gC
  have hsub : ∀ τ ∈ uIoc s t, τ ∈ Icc 0 T := fun τ hτ => by
    rw [uIoc_of_le hst] at hτ; exact ⟨hs.trans hτ.1.le, hτ.2.trans htT⟩
  have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (a := s) (b := t)
    (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun δ τ => (∫ x, (q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (rr δ τ x) +
      deriv p τ * q τ x * s113b_PhiP (p τ) ε (rr δ τ x))) +
      ∫ x, s113b_Phi1 (p τ) ε (rr δ τ x) * s113b_comm m δ b (u τ) x)
    (f := fun τ => ∫ x, (q τ x * s113b_R ν b q τ x * s113b_Theta (p τ) ε (r0 τ x) +
      deriv p τ * q τ x * s113b_PhiP (p τ) ε (r0 τ x))) (fun _ => CB + CC)
    (hev.mono fun δ hδ => ((mB δ hδ).add (mC δ hδ)).aestronglyMeasurable)
    (hev.mono fun δ hδ => ae_of_all _ fun τ hτ => by
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (add_le_add (bB δ hδ τ (hsub τ hτ)) (bC δ hδ τ (hsub τ hτ))))
    intervalIntegrable_const
    (ae_of_all _ fun τ hτ => by
      simpa using (tB τ (hsub τ hτ)).add (tC τ (hsub τ hτ)))
  have hA := (tA t htI).sub (tA s hsI)
  refine le_of_tendsto_of_tendsto hA hlim (hev.mono fun δ hδ => ?_)
  exact s113b_mollified_chain hD m hp hp1 hε hδ.1
    ((Metric.cthickening_mono (by linarith [hδ.2]) K).trans hδ1G) hs hst htT

end HRS.MS.S113X2B
