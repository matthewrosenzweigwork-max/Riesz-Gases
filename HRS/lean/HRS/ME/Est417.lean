import HRS.Stochastic.LyonsZhengSpec

/-!
# Row 4.17, packets M3 and M4b: proofs of `ibp_weighted` and `martingale_window_bound`

Statements copied verbatim from `HRS/ME/Spec417Est.lean`.  Helper lemmas carry the prefix `est3` / `est4`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.ME

open HRS HRS.LZ

/-- Triangle slice: the integral over `(0, b]` of the truncated integrand is the integral over `(0, x]`. -/
theorem est3_slice (f : ℝ → ℝ) (b x : ℝ) (hxb : x ≤ b) :
    ∫ v in Set.Ioc (0:ℝ) b, (if v ≤ x then f v else 0) = ∫ v in Set.Ioc (0:ℝ) x, f v := by
  have h1 : (fun v => if v ≤ x then f v else 0) = (Set.Iic x).indicator f := by
    funext v
    by_cases hv : v ≤ x
    · simp [Set.indicator_apply, hv]
    · simp [Set.indicator_apply, hv]
  rw [h1, MeasureTheory.setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic, min_eq_right hxb]

/-- Fubini on the triangle `0 ≤ v ≤ b - r ≤ b`. -/
theorem est3_fubini (b : ℝ) (hb : 0 ≤ b) (G g : ℝ → ℝ)
    (hG : IntervalIntegrable G volume 0 b) (hg : ContinuousOn g (Set.Icc 0 b)) :
    ∫ r in (0:ℝ)..b, (∫ v in (0:ℝ)..(b - r), g v) * G r =
      ∫ v in (0:ℝ)..b, g v * ∫ r in (0:ℝ)..(b - v), G r := by
  -- clamped version of `g`: continuous and bounded on `ℝ`, equal to `g` on `[0, b]`
  set gc : ℝ → ℝ := fun v => g (max 0 (min v b)) with hgc_def
  have hclamp_cont : Continuous fun v : ℝ => max 0 (min v b) := by fun_prop
  have hclamp_mem : ∀ v : ℝ, max 0 (min v b) ∈ Set.Icc (0:ℝ) b := fun v =>
    ⟨le_max_left _ _, max_le hb (min_le_right _ _)⟩
  have hgc_cont : Continuous gc := by
    have h : ContinuousOn (g ∘ fun v : ℝ => max 0 (min v b)) Set.univ :=
      hg.comp hclamp_cont.continuousOn (fun v _ => hclamp_mem v)
    exact continuousOn_univ.mp h
  have hgc_eq : ∀ v ∈ Set.Icc (0:ℝ) b, gc v = g v := fun v hv => by
    simp only [hgc_def]
    rw [min_eq_left hv.2, max_eq_right hv.1]
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := b)).exists_bound_of_continuousOn hg
  set M : ℝ := max M0 0 with hMdef
  have hM : ∀ v, ‖gc v‖ ≤ M := fun v => by
    have := hM0 _ (hclamp_mem v)
    exact le_trans this (le_max_left _ _)
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) b) with hμ
  have hGi : Integrable G μ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 hG
  -- the kernel
  set F : ℝ → ℝ → ℝ := fun r v => Set.indicator {p : ℝ × ℝ | p.2 ≤ b - p.1}
      (fun p => gc p.2 * G p.1) (r, v) with hF
  have hFv : ∀ r v, F r v = if v ≤ b - r then gc v * G r else 0 := by
    intro r v
    simp [hF, Set.indicator_apply]
  have hFmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod μ) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => gc p.2 * G p.1) (μ.prod μ) :=
      ((hgc_cont.measurable.comp measurable_snd).aestronglyMeasurable).mul
        (hGi.aestronglyMeasurable.comp_fst)
    have h2 : AEStronglyMeasurable
        ({p : ℝ × ℝ | p.2 ≤ b - p.1}.indicator (fun p : ℝ × ℝ => gc p.2 * G p.1)) (μ.prod μ) :=
      h1.indicator (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
    exact h2
  have hint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hb1 : Integrable (fun p : ℝ × ℝ => ‖G p.1‖ * (1:ℝ)) (μ.prod μ) :=
      Integrable.mul_prod hGi.norm (integrable_const (1:ℝ))
    have hb2 : Integrable (fun p : ℝ × ℝ => M * (‖G p.1‖ * (1:ℝ))) (μ.prod μ) := hb1.const_mul M
    refine hb2.mono' hFmeas ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    show ‖F p.1 p.2‖ ≤ M * (‖G p.1‖ * 1)
    rw [hFv, mul_one]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM p.2) (norm_nonneg _)
    · simp only [norm_zero]
      exact mul_nonneg hM_nonneg (norm_nonneg _)
  have hswap := MeasureTheory.integral_integral_swap (μ := μ) (ν := μ) (f := F) hint
  -- left side
  have hL : ∫ r in (0:ℝ)..b, (∫ v in (0:ℝ)..(b - r), g v) * G r = ∫ x, ∫ y, F x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hb]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    have h0 : 0 ≤ b - r := by linarith [hr.2]
    have h1 : b - r ≤ b := by linarith [hr.1]
    have hsl := est3_slice (fun y => gc y * G r) b (b - r) h1
    simp only [hFv]
    rw [hsl, MeasureTheory.integral_mul_const, ← intervalIntegral.integral_of_le h0]
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le h0] at hy
    exact (hgc_eq y ⟨hy.1, le_trans hy.2 (by linarith [hr.1])⟩).symm
  -- right side
  have hR : ∫ y, ∫ x, F x y ∂μ ∂μ = ∫ v in (0:ℝ)..b, g v * ∫ r in (0:ℝ)..(b - v), G r := by
    rw [intervalIntegral.integral_of_le hb]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    have h1 : ∀ x, F x v = gc v * (if x ≤ b - v then G x else 0) := by
      intro x
      have hiff : (v ≤ b - x) ↔ (x ≤ b - v) := le_sub_comm
      simp only [hFv, hiff]
      split_ifs <;> simp
    simp only [h1]
    rw [MeasureTheory.integral_const_mul, est3_slice G b (b - v) (by linarith [hv.1]),
      ← intervalIntegral.integral_of_le (by linarith [hv.2] : (0:ℝ) ≤ b - v)]
    rw [hgc_eq v ⟨hv.1.le, hv.2⟩]
  have hLHS := hL
  rw [hLHS, hswap, hR]

theorem ibp_weighted_proof (G γ γ' : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hG : IntervalIntegrable G volume 0 b)
    (hγ : ∀ x ∈ Set.Icc 0 b, HasDerivWithinAt γ (γ' x) (Set.Icc 0 b) x) (hγ' : ContinuousOn γ' (Set.Icc 0 b)) :
    ∫ r in (0 : ℝ)..b, γ (b - r) * G r =
      γ 0 * (∫ r in (0 : ℝ)..b, G r) + ∫ r in (0 : ℝ)..b, γ' (b - r) * ∫ u in (0 : ℝ)..r, G u := by
  have hu : Set.uIcc (0:ℝ) b = Set.Icc 0 b := Set.uIcc_of_le hb
  -- the triangle representation `γ(b - r) - γ 0 = ∫_0^{b-r} γ'`
  have htri : ∀ r ∈ Set.uIcc (0:ℝ) b, ∫ v in (0:ℝ)..(b - r), γ' v = γ (b - r) - γ 0 := by
    intro r hr
    rw [hu] at hr
    have h0 : 0 ≤ b - r := by linarith [hr.2]
    have hsub : Set.Icc (0:ℝ) (b - r) ⊆ Set.Icc 0 b := fun x hx =>
      ⟨hx.1, by linarith [hx.2, hr.1]⟩
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0
    · exact fun x hx => ((hγ x (hsub hx)).continuousWithinAt).mono hsub
    · intro x hx
      have hxb : x < b := by linarith [hx.2, hr.1]
      exact (hγ x ⟨hx.1.le, hxb.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hxb)
    · exact (ContinuousOn.mono hγ' hsub).intervalIntegrable_of_Icc h0
  have hγc : ContinuousOn γ (Set.Icc 0 b) := fun x hx => (hγ x hx).continuousWithinAt
  have hmapsto : Set.MapsTo (fun r : ℝ => b - r) (Set.uIcc 0 b) (Set.Icc 0 b) := by
    intro r hr
    rw [hu] at hr
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hcont1 : ContinuousOn (fun r : ℝ => γ (b - r) - γ 0) (Set.uIcc 0 b) := by
    have h1 : ContinuousOn (fun r : ℝ => b - r) (Set.uIcc 0 b) :=
      (continuous_const.sub continuous_id).continuousOn
    exact (hγc.comp h1 hmapsto).sub continuousOn_const
  have hcontΦ : ContinuousOn (fun r : ℝ => ∫ v in (0:ℝ)..(b - r), γ' v) (Set.uIcc 0 b) :=
    hcont1.congr htri
  have hint2 : IntervalIntegrable (fun r => (∫ v in (0:ℝ)..(b - r), γ' v) * G r) volume 0 b :=
    IntervalIntegrable.continuousOn_mul hG hcontΦ
  have hLHS : ∫ r in (0:ℝ)..b, γ (b - r) * G r =
      γ 0 * (∫ r in (0:ℝ)..b, G r) + ∫ r in (0:ℝ)..b, (∫ v in (0:ℝ)..(b - r), γ' v) * G r := by
    have h1 : ∫ r in (0:ℝ)..b, γ (b - r) * G r =
        ∫ r in (0:ℝ)..b, (γ 0 * G r + (∫ v in (0:ℝ)..(b - r), γ' v) * G r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      simp only
      rw [htri r hr]
      ring
    rw [h1, intervalIntegral.integral_add (hG.const_mul (γ 0)) hint2,
      intervalIntegral.integral_const_mul]
  have hFub := est3_fubini b hb G γ' hG hγ'
  have hcomp : ∫ v in (0:ℝ)..b, γ' v * (∫ r in (0:ℝ)..(b - v), G r) =
      ∫ r in (0:ℝ)..b, γ' (b - r) * ∫ u in (0:ℝ)..r, G u := by
    have := intervalIntegral.integral_comp_sub_left
      (fun v => γ' v * ∫ r in (0:ℝ)..(b - v), G r) (a := 0) (b := b) b
    simp only [sub_self, sub_zero, sub_sub_cancel] at this
    exact this.symm
  rw [hLHS, hFub, hcomp]

/-! ### M4b helpers -/

theorem est4_ratTimes_countable (u T : ℝ) : (ratTimes u T).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range (fun q : ℚ => (q : ℝ)))
  intro t ht
  have ht' : t ∈ Set.Icc u (u + T) ∧ ∃ q : ℚ, (q : ℝ) = t := ht
  obtain ⟨_, q, hq⟩ := ht'
  exact ⟨q, hq⟩

theorem est4_meas_sup {Ω : Type*} [MeasurableSpace Ω] (S : Set ℝ) (hS : S.Countable)
    (F : ℝ → Ω → ℝ≥0∞) (hF : ∀ v, Measurable (F v)) :
    Measurable (fun ω => ⨆ v ∈ S, F v ω) := by
  haveI : Countable S := hS.to_subtype
  have h : (fun ω => ⨆ v ∈ S, F v ω) = fun ω => ⨆ v : S, F v ω := by
    funext ω
    exact (iSup_subtype'' S (fun v => F v ω)).symm
  rw [h]
  exact Measurable.iSup (fun v : S => hF v)

/-- Density of the rational times: the sup over `ℚ ∩ [u, u+T]` dominates the value at any point of
the window, where the function vanishes at the left endpoint. -/
theorem est4_density (f : ℝ → ℝ) (hf : Continuous f) (u T x : ℝ) (hT : 0 ≤ T)
    (hx : x ∈ Set.Icc u (u + T)) (hfu : f u = 0) :
    ENNReal.ofReal (f x) ≤ ⨆ v ∈ ratTimes u T, ENNReal.ofReal (f v) := by
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · have hxu : x = u := le_antisymm (by linarith [hx.2]) hx.1
    rw [hxu, hfu]
    simp
  · have hcl : x ∈ closure (ratTimes u T) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hL : max u (x - ε) < min (u + T) (x + ε) :=
        max_lt (lt_min (by linarith) (by linarith [hx.1]))
          (lt_min (by linarith [hx.2]) (by linarith))
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hL
      have hq1' : u ≤ (q : ℝ) := le_trans (le_max_left _ _) hq1.le
      have hq2' : (q : ℝ) ≤ u + T := le_trans hq2.le (min_le_left _ _)
      refine ⟨(q : ℝ), ⟨⟨hq1', hq2'⟩, q, rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [le_max_right u (x - ε), min_le_right (u + T) (x + ε)]
      · linarith [le_max_right u (x - ε), min_le_right (u + T) (x + ε)]
    haveI : (𝓝[ratTimes u T] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have ht : Tendsto (fun v => ENNReal.ofReal (f v)) (𝓝[ratTimes u T] x)
        (𝓝 (ENNReal.ofReal (f x))) :=
      ((ENNReal.continuous_ofReal.comp hf).tendsto x).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht (Filter.eventually_of_mem self_mem_nhdsWithin (fun v hv => ?_))
    exact le_iSup₂ (f := fun v (_ : v ∈ ratTimes u T) => ENNReal.ofReal (f v)) v hv

/-- Weighted Cauchy-Schwarz: `(∫ g|X|)² ≤ (∫ g)(∫ g X²)` for a nonnegative weight. -/
theorem est4_cs (a : ℝ) (ha : 0 ≤ a) (g X : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ r, 0 ≤ g r)
    (hX : Continuous X) :
    (∫ r in (0:ℝ)..a, g r * |X r|) ^ 2 ≤
      (∫ r in (0:ℝ)..a, g r) * ∫ r in (0:ℝ)..a, g r * X r ^ 2 := by
  have hF_int : IntervalIntegrable (fun r => g r * |X r|) volume 0 a :=
    (hg.mul hX.abs).intervalIntegrable _ _
  have hB_int : IntervalIntegrable g volume 0 a := hg.intervalIntegrable _ _
  have hQ_int : IntervalIntegrable (fun r => g r * X r ^ 2) volume 0 a :=
    (hg.mul (hX.pow 2)).intervalIntegrable _ _
  have hB0 : 0 ≤ ∫ r in (0:ℝ)..a, g r :=
    intervalIntegral.integral_nonneg ha (fun r _ => hg0 r)
  have hQ0 : 0 ≤ ∫ r in (0:ℝ)..a, g r * X r ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun r _ => mul_nonneg (hg0 r) (sq_nonneg _))
  have hquad : ∀ l : ℝ, 0 ≤ (∫ r in (0:ℝ)..a, g r * X r ^ 2)
      - 2 * l * (∫ r in (0:ℝ)..a, g r * |X r|) + l ^ 2 * ∫ r in (0:ℝ)..a, g r := by
    intro l
    have h1 : 0 ≤ ∫ r in (0:ℝ)..a, g r * (|X r| - l) ^ 2 :=
      intervalIntegral.integral_nonneg ha (fun r _ => mul_nonneg (hg0 r) (sq_nonneg _))
    have e : (fun r => g r * (|X r| - l) ^ 2) =
        fun r => (g r * X r ^ 2 - (2 * l) * (g r * |X r|)) + l ^ 2 * g r := by
      funext r
      have h : (|X r| - l) ^ 2 = X r ^ 2 - 2 * l * |X r| + l ^ 2 := by
        rw [← sq_abs (X r)]
        ring
      rw [h]
      ring
    have h2 : ∫ r in (0:ℝ)..a, g r * (|X r| - l) ^ 2 =
        (∫ r in (0:ℝ)..a, g r * X r ^ 2) - 2 * l * (∫ r in (0:ℝ)..a, g r * |X r|)
          + l ^ 2 * ∫ r in (0:ℝ)..a, g r := by
      rw [e, intervalIntegral.integral_add (hQ_int.sub (hF_int.const_mul (2 * l)))
        (hB_int.const_mul (l ^ 2)),
        intervalIntegral.integral_sub hQ_int (hF_int.const_mul (2 * l)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith
  set F := ∫ r in (0:ℝ)..a, g r * |X r| with hFdef
  set B := ∫ r in (0:ℝ)..a, g r with hBdef
  set Q := ∫ r in (0:ℝ)..a, g r * X r ^ 2 with hQdef
  rcases eq_or_lt_of_le hB0 with hB00 | hBpos
  · have hF0 : F = 0 := by
      by_contra hne
      have h := hquad ((Q + 1) / F)
      rw [← hB00] at h
      have e2 : 2 * ((Q + 1) / F) * F = 2 * (Q + 1) := by field_simp
      linarith
    rw [hF0, ← hB00]
    simp
  · have h := hquad (F / B)
    have key : B * (Q - 2 * (F / B) * F + (F / B) ^ 2 * B) = B * Q - F ^ 2 := by
      field_simp
      ring
    have := mul_nonneg hBpos.le h
    linarith

/-- `∫_0^a e^{-c w} dw ≤ 1/c`. -/
theorem est4_int_exp1 (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    ∫ w in (0:ℝ)..a, Real.exp (-c * w) ≤ 1 / c := by
  have hc0 : c ≠ 0 := hc.ne'
  have hd : ∀ w ∈ Set.uIcc (0:ℝ) a,
      HasDerivAt (fun w : ℝ => -Real.exp (-c * w) / c) (Real.exp (-c * w)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => -c * w) (-c) w := by
      simpa using (hasDerivAt_id' w).const_mul (-c)
    have h2 := ((h1.exp).neg).div_const c
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  have he : 0 ≤ Real.exp (-c * a) / c := div_nonneg (Real.exp_pos _).le hc.le
  have key : -Real.exp (-c * a) / c - -1 / c = -(Real.exp (-c * a) / c) + 1 / c := by ring
  rw [key]
  linarith

/-- `∫_0^a w e^{-c w} dw ≤ 1/c²`. -/
theorem est4_int_exp2 (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    ∫ w in (0:ℝ)..a, w * Real.exp (-c * w) ≤ 1 / c ^ 2 := by
  have hc0 : c ≠ 0 := hc.ne'
  have hd : ∀ w ∈ Set.uIcc (0:ℝ) a,
      HasDerivAt (fun w : ℝ => -((w / c + 1 / c ^ 2) * Real.exp (-c * w)))
        (w * Real.exp (-c * w)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => -c * w) (-c) w := by
      simpa using (hasDerivAt_id' w).const_mul (-c)
    have h2 : HasDerivAt (fun w : ℝ => w / c + 1 / c ^ 2) (1 / c) w :=
      ((hasDerivAt_id' w).div_const c).add_const _
    have h3 := (h2.mul h1.exp).neg
    convert h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [zero_div, zero_add, mul_zero, Real.exp_zero, mul_one]
  have hnn : 0 ≤ (a / c + 1 / c ^ 2) * Real.exp (-c * a) :=
    mul_nonneg (add_nonneg (div_nonneg ha hc.le) (by positivity)) (Real.exp_pos _).le
  linarith

/-- `∫_0^a e^{-c(a-r)} dr ≤ 1/c`. -/
theorem est4_int_g (c : ℝ) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a) :
    ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) ≤ 1 / c := by
  have h := intervalIntegral.integral_comp_sub_left (fun w : ℝ => Real.exp (-c * w)) a
    (a := 0) (b := a)
  simp only [sub_self, sub_zero] at h
  rw [h]
  exact est4_int_exp1 c hc a ha

/-- FTC for `r ↦ γ'(y - r)` on `[0, x]` with `y - x ≥ 0`. -/
theorem est4_ftc (γ γ' : ℝ → ℝ) (hγ : ∀ x, 0 < x → HasDerivAt γ (γ' x) x)
    (hγc : ContinuousOn γ (Set.Ici 0)) (hγ' : Continuous γ') (y x : ℝ) (hx : 0 ≤ x)
    (hyx : 0 ≤ y - x) :
    ∫ r in (0:ℝ)..x, γ' (y - r) = γ y - γ (y - x) := by
  rw [intervalIntegral.integral_comp_sub_left γ' y, sub_zero]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith)
  · exact hγc.mono (fun v hv => le_trans hyx hv.1)
  · intro v hv
    exact hγ v (hyx.trans_lt hv.1)
  · exact hγ'.intervalIntegrable _ _

/-- Pathwise decomposition of `S(a+t)`. -/
theorem est4_decomp (M γ γ' : ℝ → ℝ) (hM : Continuous M) (hγ : ∀ x, 0 < x → HasDerivAt γ (γ' x) x)
    (hγc : ContinuousOn γ (Set.Ici 0)) (hγ' : Continuous γ') (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    γ 0 * M (a + t) + ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * M r =
      γ (a + t) * M a + (γ 0 * (M (a + t) - M a) +
        ∫ s in (0:ℝ)..t, γ' (t - s) * (M (a + s) - M a))
        - ∫ r in (0:ℝ)..a, γ' (a + t - r) * (M a - M r) := by
  have hc1 : Continuous fun r => γ' (a + t - r) * M r := by fun_prop
  have hsplit : ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * M r =
      (∫ r in (0:ℝ)..a, γ' (a + t - r) * M r) + ∫ r in a..(a + t), γ' (a + t - r) * M r := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc1.intervalIntegrable 0 a)
      (hc1.intervalIntegrable a (a + t))]
  have hII : ∫ r in a..(a + t), γ' (a + t - r) * M r =
      ∫ s in (0:ℝ)..t, γ' (t - s) * M (a + s) := by
    have h := intervalIntegral.integral_comp_add_left (fun r => γ' (a + t - r) * M r) a
      (a := 0) (b := t)
    rw [add_zero] at h
    simp only [show ∀ s : ℝ, a + t - (a + s) = t - s from fun s => by ring] at h
    exact h.symm
  have hIII : ∫ s in (0:ℝ)..t, γ' (t - s) * M (a + s) =
      (∫ s in (0:ℝ)..t, γ' (t - s) * (M (a + s) - M a)) + M a * (γ t - γ 0) := by
    have e : ∀ s : ℝ, γ' (t - s) * M (a + s) =
        γ' (t - s) * (M (a + s) - M a) + M a * γ' (t - s) := fun s => by ring
    simp_rw [e]
    have hc2 : Continuous fun s : ℝ => γ' (t - s) * (M (a + s) - M a) := by fun_prop
    have hc3 : Continuous fun s : ℝ => M a * γ' (t - s) := by fun_prop
    have hf := est4_ftc γ γ' hγ hγc hγ' t t ht (by linarith)
    rw [sub_self] at hf
    rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) (hc3.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hf]
  have hIV : ∫ r in (0:ℝ)..a, γ' (a + t - r) * M r =
      M a * (γ (a + t) - γ t) - ∫ r in (0:ℝ)..a, γ' (a + t - r) * (M a - M r) := by
    have e : ∀ r : ℝ, γ' (a + t - r) * (M a - M r) =
        M a * γ' (a + t - r) - γ' (a + t - r) * M r := fun r => by ring
    simp_rw [e]
    have h1 : Continuous fun r : ℝ => M a * γ' (a + t - r) := by fun_prop
    have h2 : Continuous fun r : ℝ => γ' (a + t - r) * M r := by fun_prop
    have hf := est4_ftc γ γ' hγ hγc hγ' (a + t) a ha (by linarith)
    rw [add_sub_cancel_left] at hf
    rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hf]
    ring
  rw [hsplit, hII, hIII, hIV]
  ring

/-- Three-term square bound. -/
theorem est4_sq3 (X Y Z P1 P2 P3 : ℝ) (hX : X ^ 2 ≤ P1) (hY : Y ^ 2 ≤ P2) (hZ : Z ^ 2 ≤ P3) :
    (X + Y - Z) ^ 2 ≤ 3 * (P1 + P2 + P3) := by
  nlinarith [sq_nonneg (X - Y), sq_nonneg (Y + Z), sq_nonneg (X + Z)]

/-- Pathwise bound of `S(a+t)²` for a single continuous path, with `q` dominating the squared
increments on the window. -/
theorem est4_real_bound (m γ γ' : ℝ → ℝ) (hm : Continuous m) (c Γ a T t q : ℝ) (hc : 0 < c)
    (hΓ : 0 ≤ Γ) (ha : 0 ≤ a) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T) (hq0 : 0 ≤ q)
    (hγ : ∀ x, 0 < x → HasDerivAt γ (γ' x) x) (hγc : ContinuousOn γ (Set.Ici 0))
    (hγ' : Continuous γ')
    (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v))
    (hq : ∀ s, 0 ≤ s → s ≤ T → (m (a + s) - m a) ^ 2 ≤ q) :
    (γ 0 * m (a + t) + ∫ r in (0:ℝ)..(a + t), γ' (a + t - r) * m r) ^ 2 ≤
      3 * ((Γ * Real.exp (-c * a)) ^ 2 * m a ^ 2 + (Γ * (1 + T)) ^ 2 * q +
        Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2) := by
  rw [est4_decomp m γ γ' hm hγ hγc hγ' a t ha ht]
  -- the three terms
  have hK : |γ (a + t)| ≤ Γ * Real.exp (-c * a) := by
    have h1 := (hbd (a + t) (by linarith)).1
    have h2 : Real.exp (-c * (a + t)) ≤ Real.exp (-c * a) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc.le ht])
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hΓ)
  have hx2 : (γ (a + t) * m a) ^ 2 ≤ (Γ * Real.exp (-c * a)) ^ 2 * m a ^ 2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have h3 := mul_le_mul hK hK (abs_nonneg _) (le_trans (abs_nonneg _) hK)
    nlinarith [sq_abs (γ (a + t))]
  have hρ0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hρq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0
  have hd : ∀ s, 0 ≤ s → s ≤ T → |m (a + s) - m a| ≤ Real.sqrt q :=
    fun s hs0 hsT => Real.abs_le_sqrt (hq s hs0 hsT)
  have hg0 : |γ 0| ≤ Γ := by simpa using (hbd 0 le_rfl).1
  have hgt : ∀ s ∈ Set.uIoc (0:ℝ) t, ‖γ' (t - s) * (m (a + s) - m a)‖ ≤ Γ * Real.sqrt q := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hst : 0 ≤ t - s := by linarith [hs.2]
    have hγb : |γ' (t - s)| ≤ Γ := by
      have h1 := (hbd (t - s) hst).2
      have hexp : Real.exp (-c * (t - s)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hc.le hst])
      exact h1.trans (mul_le_of_le_one_right hΓ hexp)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hγb (hd s hs0 (by linarith [hs.2])) (abs_nonneg _) hΓ
  have hIy := intervalIntegral.norm_integral_le_of_norm_le_const hgt
  have hyabs : |γ 0 * (m (a + t) - m a) + ∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a)|
      ≤ Γ * (1 + T) * Real.sqrt q := by
    have h1 : |γ 0 * (m (a + t) - m a)| ≤ Γ * Real.sqrt q := by
      rw [abs_mul]
      exact mul_le_mul hg0 (hd t ht htT) (abs_nonneg _) hΓ
    have h2 : |∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a)| ≤ Γ * Real.sqrt q * t := by
      have h := hIy
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
      exact h
    have h3 := abs_add_le (γ 0 * (m (a + t) - m a))
      (∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a))
    have h4 : Γ * Real.sqrt q * t ≤ Γ * Real.sqrt q * T :=
      mul_le_mul_of_nonneg_left htT (mul_nonneg hΓ hρ0)
    nlinarith
  have hy2 : (γ 0 * (m (a + t) - m a) + ∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a)) ^ 2
      ≤ (Γ * (1 + T)) ^ 2 * q := by
    have hK2 : (Γ * (1 + T) * Real.sqrt q) ^ 2 = (Γ * (1 + T)) ^ 2 * q := by
      rw [mul_pow, hρq]
    have hm' := mul_le_mul hyabs hyabs (abs_nonneg _)
      (mul_nonneg (mul_nonneg hΓ (by linarith)) hρ0)
    have hyy : (γ 0 * (m (a + t) - m a) + ∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a)) ^ 2
        ≤ (Γ * (1 + T) * Real.sqrt q) ^ 2 := by
      rw [sq, ← abs_mul_abs_self]
      nlinarith [abs_mul_abs_self (γ 0 * (m (a + t) - m a) +
        ∫ s in (0:ℝ)..t, γ' (t - s) * (m (a + s) - m a))]
    linarith [hK2, hyy]
  -- the stochastic term
  have hW : |∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)| ≤
      Γ * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r| := by
    have hgint : Continuous fun r : ℝ => Γ * (Real.exp (-c * (a - r)) * |m a - m r|) := by
      fun_prop
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun r => γ' (a + t - r) * (m a - m r)) ha
      (Filter.Eventually.of_forall (fun r => fun hr => by
        have hra : r ≤ a := hr.2
        have hA : |γ' (a + t - r)| ≤ Γ * Real.exp (-c * (a - r)) :=
          (hbd (a + t - r) (by linarith [hr.1])).2.trans
            (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hc.le ht])) hΓ)
        rw [Real.norm_eq_abs, abs_mul]
        calc |γ' (a + t - r)| * |m a - m r| ≤ (Γ * Real.exp (-c * (a - r))) * |m a - m r| :=
              mul_le_mul_of_nonneg_right hA (abs_nonneg _)
          _ = Γ * (Real.exp (-c * (a - r)) * |m a - m r|) := by ring))
      (hgint.intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hle
    exact hle
  have hDv0 : 0 ≤ ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun r _ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hcs := est4_cs a ha (fun r => Real.exp (-c * (a - r))) (fun r => m a - m r)
    (by fun_prop) (fun r => (Real.exp_pos _).le) (by fun_prop)
  have hgle := est4_int_g c hc a ha
  have hW2 : (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r|) ^ 2 ≤
      1 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hgle hDv0)
  have hz2 : (∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)) ^ 2 ≤
      Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2 := by
    have hW0 : 0 ≤ ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r| :=
      intervalIntegral.integral_nonneg ha
        (fun r _ => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
    have hzz : (∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)) ^ 2 =
        |∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)| *
          |∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)| := by
      rw [abs_mul_abs_self]
      ring
    have h1 : (∫ r in (0:ℝ)..a, γ' (a + t - r) * (m a - m r)) ^ 2 ≤
        (Γ * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r|) ^ 2 := by
      rw [hzz, sq]
      exact mul_le_mul hW hW (abs_nonneg _) (mul_nonneg hΓ hW0)
    have h2 : (Γ * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r|) ^ 2 =
        Γ ^ 2 * (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * |m a - m r|) ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_left hW2 (sq_nonneg Γ)
    have h4 : Γ ^ 2 * (1 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2) =
        Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (m a - m r) ^ 2 := by ring
    linarith
  exact est4_sq3 _ _ _ _ _ _ hx2 hy2 hz2

/-- Endpoint term: `E (M_a)² ≤ κ a`. -/
theorem est4_A_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ℝ → Ω → ℝ) (hmeas : ∀ t, Measurable (M t)) (hcont : ∀ ω, Continuous (fun t => M t ω))
    (hM0 : ∀ ω, M 0 ω = 0) (κ a H : ℝ) (ha : 0 ≤ a) (haH : a ≤ H)
    (hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((M v ω - M u ω) ^ 2) ∂P ≤
        ENNReal.ofReal (κ * (t - u))) :
    ∫⁻ ω, ENNReal.ofReal ((M a ω) ^ 2) ∂P ≤ ENNReal.ofReal (κ * a) := by
  have h : ∀ ω, ENNReal.ofReal ((M a ω) ^ 2) ≤
      ⨆ v ∈ ratTimes 0 (a - 0), ENNReal.ofReal ((M v ω - M 0 ω) ^ 2) := by
    intro ω
    have h1 := est4_density (fun v => (M v ω - M 0 ω) ^ 2) (by have := hcont ω; fun_prop)
      0 (a - 0) a (by linarith) ⟨ha, by linarith⟩ (by simp [hM0 ω])
    simp only [hM0 ω, sub_zero] at h1 ⊢
    exact h1
  calc ∫⁻ ω, ENNReal.ofReal ((M a ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ⨆ v ∈ ratTimes 0 (a - 0), ENNReal.ofReal ((M v ω - M 0 ω) ^ 2) ∂P := lintegral_mono h
    _ ≤ ENNReal.ofReal (κ * (a - 0)) := hmax 0 a le_rfl ha haH
    _ = ENNReal.ofReal (κ * a) := by rw [sub_zero]

/-- Tonelli bound for the weighted Cauchy-Schwarz term. -/
theorem est4_D_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ℝ → Ω → ℝ) (hmeas : ∀ t, Measurable (M t))
    (hjoint : Measurable (fun p : ℝ × Ω => M p.1 p.2)) (hcont : ∀ ω, Continuous (fun t => M t ω))
    (c κ a H : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (haH : a ≤ H) (hκ : 0 ≤ κ)
    (hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((M v ω - M u ω) ^ 2) ∂P ≤
        ENNReal.ofReal (κ * (t - u))) :
    ∫⁻ ω, ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) ∂P ≤
      ENNReal.ofReal (κ / c ^ 2) := by
  have hgc : Continuous (fun r : ℝ => Real.exp (-c * (a - r))) := by fun_prop
  have hmeasf : Measurable (fun p : Ω × ℝ =>
      Real.exp (-c * (a - p.2)) * (M a p.1 - M p.2 p.1) ^ 2) := by
    have hMr : Measurable (fun p : Ω × ℝ => M p.2 p.1) := hjoint.comp measurable_swap
    have hMa : Measurable (fun p : Ω × ℝ => M a p.1) := (hmeas a).comp measurable_fst
    exact (hgc.measurable.comp measurable_snd).mul ((hMa.sub hMr).pow_const 2)
  have hDeq : ∀ ω, ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2)
      = ∫⁻ r in Set.Ioc (0:ℝ) a, ENNReal.ofReal (Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) := by
    intro ω
    rw [intervalIntegral.integral_of_le ha]
    have hc' : Continuous (fun r : ℝ => Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) := by
      have := hcont ω
      fun_prop
    exact ofReal_integral_eq_lintegral_ofReal hc'.integrableOn_Ioc
      (Filter.Eventually.of_forall (fun r => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)))
  have hmeasE : Measurable (Function.uncurry (fun (ω : Ω) (r : ℝ) =>
      ENNReal.ofReal (Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2))) :=
    hmeasf.ennreal_ofReal
  have hinner : ∀ r ∈ Set.Ioc (0:ℝ) a, ∫⁻ ω, ENNReal.ofReal (Real.exp (-c * (a - r)) *
      (M a ω - M r ω) ^ 2) ∂P ≤
      ENNReal.ofReal (κ * ((a - r) * Real.exp (-c * (a - r)))) := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hra : r ≤ a := hr.2
    have hmeasX : Measurable (fun ω => ENNReal.ofReal ((M a ω - M r ω) ^ 2)) :=
      (((hmeas a).sub (hmeas r)).pow_const 2).ennreal_ofReal
    have hdens : ∀ ω, ENNReal.ofReal ((M a ω - M r ω) ^ 2) ≤
        ⨆ v ∈ ratTimes r (a - r), ENNReal.ofReal ((M v ω - M r ω) ^ 2) := by
      intro ω
      exact est4_density (fun v => (M v ω - M r ω) ^ 2) (by have := hcont ω; fun_prop)
        r (a - r) a (by linarith) ⟨hra, by linarith⟩ (by simp)
    have h2 : ∫⁻ ω, ENNReal.ofReal ((M a ω - M r ω) ^ 2) ∂P ≤ ENNReal.ofReal (κ * (a - r)) :=
      le_trans (lintegral_mono hdens) (hmax r a hr0 hra haH)
    have he : ∀ ω, ENNReal.ofReal (Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) =
        ENNReal.ofReal (Real.exp (-c * (a - r))) * ENNReal.ofReal ((M a ω - M r ω) ^ 2) :=
      fun ω => ENNReal.ofReal_mul (Real.exp_nonneg _)
    simp_rw [he]
    rw [lintegral_const_mul _ hmeasX]
    calc ENNReal.ofReal (Real.exp (-c * (a - r))) *
          ∫⁻ ω, ENNReal.ofReal ((M a ω - M r ω) ^ 2) ∂P
        ≤ ENNReal.ofReal (Real.exp (-c * (a - r))) * ENNReal.ofReal (κ * (a - r)) :=
          by gcongr
      _ = ENNReal.ofReal (κ * ((a - r) * Real.exp (-c * (a - r)))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          congr 1
          ring
  have hI : ∫ r in (0:ℝ)..a, (a - r) * Real.exp (-c * (a - r)) ≤ 1 / c ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_left (fun w : ℝ => w * Real.exp (-c * w)) a
      (a := 0) (b := a)
    simp only [sub_self, sub_zero] at h
    rw [h]
    exact est4_int_exp2 c hc a ha
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) a)]
      (fun r => κ * ((a - r) * Real.exp (-c * (a - r)))) :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun r hr =>
      mul_nonneg hκ (mul_nonneg (by linarith [hr.2]) (Real.exp_nonneg _)))
  have hint : Integrable (fun r => κ * ((a - r) * Real.exp (-c * (a - r))))
      (volume.restrict (Set.Ioc (0:ℝ) a)) := by
    have hcont' : Continuous (fun r : ℝ => κ * ((a - r) * Real.exp (-c * (a - r)))) := by
      fun_prop
    exact hcont'.integrableOn_Ioc
  rw [lintegral_congr (fun ω => hDeq ω),
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Ioc (0:ℝ) a))
    (f := fun (ω : Ω) (r : ℝ) => ENNReal.ofReal (Real.exp (-c * (a - r)) *
      (M a ω - M r ω) ^ 2)) hmeasE.aemeasurable]
  calc ∫⁻ r in Set.Ioc (0:ℝ) a, ∫⁻ ω, ENNReal.ofReal (Real.exp (-c * (a - r)) *
        (M a ω - M r ω) ^ 2) ∂P
      ≤ ∫⁻ r in Set.Ioc (0:ℝ) a, ENNReal.ofReal (κ * ((a - r) * Real.exp (-c * (a - r)))) :=
        setLIntegral_mono' measurableSet_Ioc hinner
    _ = ENNReal.ofReal (∫ r in Set.Ioc (0:ℝ) a, κ * ((a - r) * Real.exp (-c * (a - r)))) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal (κ / c ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le ha]
        have h2 := mul_le_mul_of_nonneg_left hI hκ
        have h3 : κ * (1 / c ^ 2) = κ / c ^ 2 := by ring
        linarith

/-- Core estimate for a jointly measurable process that is continuous in time everywhere. -/
theorem est4_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ℝ → Ω → ℝ) (H κ Γ c T a : ℝ) (hc : 0 < c) (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ)
    (ha : 0 ≤ a) (haT : a + T ≤ H) (γ γ' : ℝ → ℝ)
    (hmeas : ∀ t, Measurable (M t)) (hjoint : Measurable (fun p : ℝ × Ω => M p.1 p.2))
    (hM0 : ∀ ω, M 0 ω = 0) (hcont : ∀ ω, Continuous (fun t => M t ω))
    (hmax : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((M v ω - M u ω) ^ 2) ∂P ≤
        ENNReal.ofReal (κ * (t - u)))
    (hγ : ∀ x, 0 < x → HasDerivAt γ (γ' x) x) (hγc : ContinuousOn γ (Set.Ici 0))
    (hγ' : Continuous γ')
    (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)) :
    ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2) ∂P ≤
      ENNReal.ofReal ((3 * (1 / (2 * c) + (1 + T) ^ 2 * T + 1 / c ^ 3)) * Γ ^ 2 * κ) := by
  have hQm : Measurable (fun ω => ⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) :=
    est4_meas_sup _ (est4_ratTimes_countable a T)
      (fun v ω => ENNReal.ofReal ((M v ω - M a ω) ^ 2))
      (fun v => (((hmeas v).sub (hmeas a)).pow_const 2).ennreal_ofReal)
  have hQint : ∫⁻ ω, ⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2) ∂P ≤
      ENNReal.ofReal (κ * T) := by
    have h := hmax a (a + T) ha (by linarith) haT
    rw [add_sub_cancel_left] at h
    exact h
  have hQfin : ∀ᵐ ω ∂P, (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) < ⊤ :=
    ae_lt_top hQm (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQint)
  have hDm := est4_D_bound P M hmeas hjoint hcont c κ a H hc ha (by linarith) hκ hmax
  have hAm := est4_A_bound P M hmeas hcont hM0 κ a H ha (by linarith) hmax
  have hDval_nn : ∀ ω, 0 ≤ ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2 :=
    fun ω => intervalIntegral.integral_nonneg ha
      (fun r _ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  -- pointwise bound on the event where the sup of the increments is finite
  have hpt : ∀ ω, (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) < ⊤ →
      (⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2)) ≤
        ENNReal.ofReal 3 * (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) +
          ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) +
          ENNReal.ofReal (Γ ^ 2 / c) *
            ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2)) := by
    intro ω hω
    have hQ_ne : (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) ≠ ⊤ := hω.ne
    have hq : ∀ s, 0 ≤ s → s ≤ T →
        (M (a + s) ω - M a ω) ^ 2 ≤ (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal := by
      intro s hs0 hsT
      have h1 : ENNReal.ofReal ((M (a + s) ω - M a ω) ^ 2) ≤
          ⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2) :=
        est4_density (fun v => (M v ω - M a ω) ^ 2) (by have := hcont ω; fun_prop) a T (a + s) hT
          ⟨by linarith, by linarith⟩ (by simp)
      exact (ENNReal.ofReal_le_iff_le_toReal hQ_ne).1 h1
    refine iSup₂_le (fun t ht => ?_)
    have htI : 0 ≤ t ∧ t ≤ T := ⟨ht.1.1, by linarith [ht.1.2]⟩
    have key : (γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2 ≤
        3 * ((Γ * Real.exp (-c * a)) ^ 2 * (M a ω) ^ 2 +
          (Γ * (1 + T)) ^ 2 * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal +
          Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) :=
      est4_real_bound (fun t => M t ω) γ γ' (hcont ω) c Γ a T t
        (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal hc hΓ ha hT htI.1 htI.2
        ENNReal.toReal_nonneg hγ hγc hγ' hbd hq
    have hP1 : 0 ≤ (Γ * Real.exp (-c * a)) ^ 2 * (M a ω) ^ 2 := by positivity
    have hP2 : 0 ≤ (Γ * (1 + T)) ^ 2 *
        (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal :=
      mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
    have hP3 : 0 ≤ Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2 :=
      mul_nonneg (div_nonneg (sq_nonneg _) hc.le) (hDval_nn ω)
    calc ENNReal.ofReal ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2)
        ≤ ENNReal.ofReal (3 * ((Γ * Real.exp (-c * a)) ^ 2 * (M a ω) ^ 2 +
          (Γ * (1 + T)) ^ 2 * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal +
          Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2)) :=
          ENNReal.ofReal_le_ofReal key
      _ = ENNReal.ofReal 3 * (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2 * (M a ω) ^ 2) +
          ENNReal.ofReal ((Γ * (1 + T)) ^ 2 *
            (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)).toReal) +
          ENNReal.ofReal (Γ ^ 2 / c * ∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (add_nonneg hP1 hP2) hP3,
            ENNReal.ofReal_add hP1 hP2]
      _ = ENNReal.ofReal 3 * (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) +
          ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) +
          ENNReal.ofReal (Γ ^ 2 / c) *
            ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2)) := by
          rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _),
            ENNReal.ofReal_toReal hQ_ne, ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) hc.le)]
  -- measurability of the three terms
  have hAm' : Measurable (fun ω => ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) *
      ENNReal.ofReal ((M a ω) ^ 2)) :=
    (((hmeas a).pow_const 2).ennreal_ofReal).const_mul _
  have hBm' : Measurable (fun ω => ENNReal.ofReal ((Γ * (1 + T)) ^ 2) *
      (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2))) :=
    hQm.const_mul _
  -- the three integrals
  have hA' : ∫⁻ ω, ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) ∂P ≤
      ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2 * (κ * a)) := by
    calc ∫⁻ ω, ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) ∂P
        = ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ∫⁻ ω, ENNReal.ofReal ((M a ω) ^ 2) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal (κ * a) := by gcongr
      _ = ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2 * (κ * a)) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hB' : ∫⁻ ω, ENNReal.ofReal ((Γ * (1 + T)) ^ 2) *
      (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) ∂P ≤
      ENNReal.ofReal ((Γ * (1 + T)) ^ 2 * (κ * T)) := by
    calc ∫⁻ ω, ENNReal.ofReal ((Γ * (1 + T)) ^ 2) *
          (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) ∂P
        = ENNReal.ofReal ((Γ * (1 + T)) ^ 2) *
          ∫⁻ ω, ⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2) ∂P :=
          lintegral_const_mul _ hQm
      _ ≤ ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * ENNReal.ofReal (κ * T) := by gcongr
      _ = ENNReal.ofReal ((Γ * (1 + T)) ^ 2 * (κ * T)) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hD' : ∫⁻ ω, ENNReal.ofReal (Γ ^ 2 / c) *
      ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) ∂P ≤
      ENNReal.ofReal (Γ ^ 2 / c * (κ / c ^ 2)) := by
    calc ∫⁻ ω, ENNReal.ofReal (Γ ^ 2 / c) *
          ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) ∂P
        = ENNReal.ofReal (Γ ^ 2 / c) *
          ∫⁻ ω, ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Γ ^ 2 / c) * ENNReal.ofReal (κ / c ^ 2) := by gcongr
      _ = ENNReal.ofReal (Γ ^ 2 / c * (κ / c ^ 2)) :=
          (ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) hc.le)).symm
  -- the real constant
  have hX1 : 0 ≤ (Γ * Real.exp (-c * a)) ^ 2 * (κ * a) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hκ ha)
  have hX2 : 0 ≤ (Γ * (1 + T)) ^ 2 * (κ * T) := mul_nonneg (sq_nonneg _) (mul_nonneg hκ hT)
  have hX3 : 0 ≤ Γ ^ 2 / c * (κ / c ^ 2) :=
    mul_nonneg (div_nonneg (sq_nonneg _) hc.le) (div_nonneg hκ (by positivity))
  have hca : 0 ≤ c * a := mul_nonneg hc.le ha
  have hy : c * a + 1 ≤ Real.exp (c * a) := Real.add_one_le_exp _
  have hy2 : 2 * c * a ≤ Real.exp (c * a) ^ 2 := by
    have h0 : 0 ≤ c * a + 1 := by linarith
    have hyy := mul_le_mul hy hy h0 (Real.exp_nonneg _)
    nlinarith [sq_nonneg (c * a)]
  have he : Real.exp (-c * a) * Real.exp (c * a) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsq : Real.exp (-c * a) ^ 2 * Real.exp (c * a) ^ 2 = 1 := by
    rw [← mul_pow, he, one_pow]
  have hmain : Real.exp (-c * a) ^ 2 * (2 * c * a) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (Real.exp (-c * a)))
    linarith
  have he2 : Real.exp (-c * a) ^ 2 * a ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmain]
  have hX1' : (Γ * Real.exp (-c * a)) ^ 2 * (κ * a) ≤ Γ ^ 2 * κ * (1 / (2 * c)) := by
    have e : (Γ * Real.exp (-c * a)) ^ 2 * (κ * a) = Γ ^ 2 * κ * (Real.exp (-c * a) ^ 2 * a) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left he2 (mul_nonneg (sq_nonneg _) hκ)
  have e2 : (Γ * (1 + T)) ^ 2 * (κ * T) = Γ ^ 2 * κ * ((1 + T) ^ 2 * T) := by ring
  have e3 : Γ ^ 2 / c * (κ / c ^ 2) = Γ ^ 2 * κ * (1 / c ^ 3) := by ring
  have hfin : 3 * ((Γ * Real.exp (-c * a)) ^ 2 * (κ * a) + ((Γ * (1 + T)) ^ 2 * (κ * T) +
      Γ ^ 2 / c * (κ / c ^ 2))) ≤ 3 * (1 / (2 * c) + (1 + T) ^ 2 * T + 1 / c ^ 3) * Γ ^ 2 * κ := by
    rw [e2, e3]
    have e4 : 3 * (1 / (2 * c) + (1 + T) ^ 2 * T + 1 / c ^ 3) * Γ ^ 2 * κ =
        3 * (Γ ^ 2 * κ * (1 / (2 * c))) + 3 * (Γ ^ 2 * κ * ((1 + T) ^ 2 * T)) +
          3 * (Γ ^ 2 * κ * (1 / c ^ 3)) := by ring
    rw [e4]
    linarith [hX1']
  -- the main chain
  calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal 3 * (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) +
          (ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) +
          ENNReal.ofReal (Γ ^ 2 / c) *
            ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2))) ∂P :=
        lintegral_mono_ae (hQfin.mono (fun ω hω => (hpt ω hω).trans (le_of_eq (by rw [add_assoc]))))
    _ = ENNReal.ofReal 3 * ∫⁻ ω, (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) +
          (ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) +
          ENNReal.ofReal (Γ ^ 2 / c) *
            ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2))) ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal 3 * (∫⁻ ω, ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2) * ENNReal.ofReal ((M a ω) ^ 2) ∂P +
          (∫⁻ ω, ENNReal.ofReal ((Γ * (1 + T)) ^ 2) * (⨆ v ∈ ratTimes a T, ENNReal.ofReal ((M v ω - M a ω) ^ 2)) ∂P +
          ∫⁻ ω, ENNReal.ofReal (Γ ^ 2 / c) *
            ENNReal.ofReal (∫ r in (0:ℝ)..a, Real.exp (-c * (a - r)) * (M a ω - M r ω) ^ 2) ∂P)) := by
        rw [lintegral_add_left hAm', lintegral_add_left hBm']
    _ ≤ ENNReal.ofReal 3 * (ENNReal.ofReal ((Γ * Real.exp (-c * a)) ^ 2 * (κ * a)) +
          (ENNReal.ofReal ((Γ * (1 + T)) ^ 2 * (κ * T)) + ENNReal.ofReal (Γ ^ 2 / c * (κ / c ^ 2)))) := by
        gcongr
    _ = ENNReal.ofReal (3 * ((Γ * Real.exp (-c * a)) ^ 2 * (κ * a) + ((Γ * (1 + T)) ^ 2 * (κ * T) +
          Γ ^ 2 / c * (κ / c ^ 2)))) := by
        rw [← ENNReal.ofReal_add hX2 hX3, ← ENNReal.ofReal_add hX1 (add_nonneg hX2 hX3),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    _ ≤ ENNReal.ofReal (3 * (1 / (2 * c) + (1 + T) ^ 2 * T + 1 / c ^ 3) * Γ ^ 2 * κ) :=
        ENNReal.ofReal_le_ofReal hfin

/-- M4b.  Statement copied from `HRS/ME/Spec417Est.lean` (main branch). -/
theorem martingale_window_bound_proof (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (M : ℝ → Ω → ℝ) (H κ Γ : ℝ) (hκ : 0 ≤ κ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ),
      (∀ t, Measurable (M t)) → (∀ᵐ ω ∂P, M 0 ω = 0) →
      (∀ᵐ ω ∂P, ContinuousOn (fun t => M t ω) (Set.Icc 0 H)) →
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
        ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((M v ω - M u ω) ^ 2) ∂P ≤
          ENNReal.ofReal (κ * (t - u))) →
      (∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) → ContinuousOn γ' (Set.Ici 0) →
      (∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)) →
      ∀ a : ℝ, 0 ≤ a → a + T ≤ H →
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
            ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2) ∂P ≤
          ENNReal.ofReal (C * Γ ^ 2 * κ) := by
  refine ⟨3 * (1 / (2 * c) + (1 + T) ^ 2 * T + 1 / c ^ 3), ?_, ?_⟩
  · have h1 : 0 ≤ (1 + T) ^ 2 * T := mul_nonneg (sq_nonneg _) hT
    have h2 : 0 ≤ 1 / (2 * c) := by positivity
    have h3 : 0 ≤ 1 / c ^ 3 := by positivity
    exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg h2 h1) h3)
  intro Ω _ P _ M H κ Γ hκ hΓ γ γ' hmeas hM0 hcont hmax hγ hγ'c hbd a ha haT
  classical
  have hH0 : 0 ≤ H := by linarith
  -- a measurable null set outside of which the paths are good
  have hgood : ∀ᵐ ω ∂P, M 0 ω = 0 ∧ ContinuousOn (fun t => M t ω) (Set.Icc 0 H) :=
    hM0.and hcont
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hgood_pt : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun t => M t ω) (Set.Icc 0 H) := by
    intro ω hω
    have hnot : ω ∉ {ω | ¬ (M 0 ω = 0 ∧ ContinuousOn (fun t => M t ω) (Set.Icc 0 H))} :=
      fun h => hω (hsub h)
    simpa using hnot
  -- the modified process: clamped in time, zero on the exceptional set
  let Mt : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else M (max 0 (min t H)) ω
  have hclamp_cont : Continuous fun t : ℝ => max 0 (min t H) := by fun_prop
  have hclamp_mem : ∀ t : ℝ, max 0 (min t H) ∈ Set.Icc (0:ℝ) H := fun t =>
    ⟨le_max_left _ _, max_le hH0 (min_le_right _ _)⟩
  have hMt_cont : ∀ ω, Continuous (fun t => Mt t ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · have hfun : (fun t => Mt t ω) = fun _ => (0:ℝ) := by
        funext t
        simp [Mt, hω]
      rw [hfun]
      exact continuous_const
    · have h1 : ContinuousOn (fun t => M (max 0 (min t H)) ω) Set.univ :=
        (hgood_pt ω hω).2.comp hclamp_cont.continuousOn (fun t _ => hclamp_mem t)
      have h2 : Continuous (fun t => M (max 0 (min t H)) ω) := continuousOn_univ.mp h1
      have hfun : (fun t => Mt t ω) = fun t => M (max 0 (min t H)) ω := by
        funext t
        simp [Mt, hω]
      rw [hfun]
      exact h2
  have hNm' : MeasurableSet {ω : Ω | ω ∈ N} := by rwa [Set.setOf_mem_eq]
  have hMt_meas : ∀ t, Measurable (Mt t) := fun t =>
    Measurable.ite hNm' measurable_const (hmeas _)
  have hMt_joint : Measurable (fun p : ℝ × Ω => Mt p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hMt_cont hMt_meas
  have hMt0 : ∀ ω, Mt 0 ω = 0 := by
    intro ω
    by_cases hω : ω ∈ N
    · simp [Mt, hω]
    · have hcl : max 0 (min (0:ℝ) H) = 0 := by
        rw [min_eq_left hH0, max_self]
      have h0 := (hgood_pt ω hω).1
      simp only [Mt, if_neg hω, hcl, h0]
  have hMt_eq : ∀ ω, ω ∉ N → ∀ t ∈ Set.Icc (0:ℝ) H, Mt t ω = M t ω := by
    intro ω hω t ht
    simp only [Mt, if_neg hω]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hmaxt : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((Mt v ω - Mt u ω) ^ 2) ∂P ≤
        ENNReal.ofReal (κ * (t - u)) := by
    intro u t hu hut htH
    have h1 : ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((Mt v ω - Mt u ω) ^ 2) ∂P =
        ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal ((M v ω - M u ω) ^ 2) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hNae] with ω hω
      apply iSup_congr
      intro v
      apply iSup_congr
      intro hv
      have hvI : v ∈ Set.Icc (0:ℝ) H := ⟨le_trans hu hv.1.1, le_trans hv.1.2 (by linarith)⟩
      have huI : u ∈ Set.Icc (0:ℝ) H := ⟨hu, by linarith⟩
      have e1 := hMt_eq ω hω v hvI
      have e2 := hMt_eq ω hω u huI
      simp only [e1, e2]
    rw [h1]
    exact hmax u t hu hut htH
  have hγ_new : ∀ x, 0 < x → HasDerivAt γ (γ' (max x 0)) x := fun x hx => by
    have hmx : max x 0 = x := max_eq_left hx.le
    rw [hmx]
    exact (hγ x hx.le).hasDerivAt (Ici_mem_nhds hx)
  have hγc_new : ContinuousOn γ (Set.Ici 0) := fun x hx => (hγ x hx).continuousWithinAt
  have hcoreγ' : Continuous (fun x => γ' (max x 0)) :=
    hγ'c.comp_continuous (continuous_id.max continuous_const)
      (fun x => Set.mem_Ici.mpr (le_max_right _ _))
  have hbd_new : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧
      |(fun x => γ' (max x 0)) v| ≤ Γ * Real.exp (-c * v) := by
    intro v hv
    have h := hbd v hv
    simp only [max_eq_left hv]
    exact h
  have hcore := est4_core P Mt H κ Γ c T a hc hT hκ hΓ ha haT γ (fun x => γ' (max x 0))
    hMt_meas hMt_joint hMt0 hMt_cont hmaxt hγ_new hγc_new hcoreγ' hbd_new
  have heq : ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((γ 0 * M (a + t) ω + ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω) ^ 2) ∂P =
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
        ((γ 0 * Mt (a + t) ω + ∫ r in (0 : ℝ)..(a + t), (fun x => γ' (max x 0)) (a + t - r) * Mt r ω) ^ 2)
        ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hNae] with ω hω
    apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    have htI : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1.1, by linarith [ht.1.2]⟩
    have hat : a + t ∈ Set.Icc (0:ℝ) H := ⟨by linarith [htI.1], by linarith [htI.2]⟩
    have hint : ∫ r in (0 : ℝ)..(a + t), γ' (a + t - r) * M r ω =
        ∫ r in (0 : ℝ)..(a + t), (fun x => γ' (max x 0)) (a + t - r) * Mt r ω := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [Set.uIcc_of_le (by linarith [htI.1])] at hr
      have hrI : r ∈ Set.Icc (0:ℝ) H := ⟨hr.1, by linarith [hr.2, hat.2]⟩
      have hMr : Mt r ω = M r ω := hMt_eq ω hω r hrI
      have hnn : 0 ≤ a + t - r := by linarith [hr.2]
      show γ' (a + t - r) * M r ω = γ' (max (a + t - r) 0) * Mt r ω
      rw [max_eq_left hnn, hMr]
    rw [hint, hMt_eq ω hω (a + t) hat]
  rw [heq]
  exact hcore

end HRS.ME

end
