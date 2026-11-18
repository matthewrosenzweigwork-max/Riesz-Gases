import HRS.MC.E213U12a

/-!
# Packet e213u12 (part b): the probabilistic far estimate (generic Tonelli argument)

`u12_final_bound`: if `g(ω)` is bounded, for a.e. `ω` with integrable `‖F · ω‖` on `[0,H]`, by
`K ∫_{(0,H] ∩ (-∞,b)} e^{-c(a-v)} ‖F v ω‖ dv` (`b = max (a - Rw) 0 < H`) and `F` is jointly measurable with
`E ‖F v‖ ≤ Cm` for `v ∈ [0,H]`, then `|E g| ≤ K Cm e^{-c Rw}/c`.  No measurability of `g` is needed (a non-measurable
`g` has Bochner integral `0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U12

/-- Tonelli: the weighted time integral of the `L¹(P)` norms. -/
theorem u12_tonelli {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → E)
    (hF : Measurable (Function.uncurry F)) (H C : ℝ)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) H, ∫⁻ ω, ‖F v ω‖ₑ ∂P ≤ ENNReal.ofReal C) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (s : Set ℝ) (hs : MeasurableSet s) (hsH : s ⊆ Set.Icc 0 H) :
    ∫⁻ ω, (∫⁻ v in s, w v * ‖F v ω‖ₑ) ∂P ≤ ENNReal.ofReal C * ∫⁻ v in s, w v := by
  have hm : Measurable (fun p : Ω × ℝ => w p.2 * ‖F p.2 p.1‖ₑ) :=
    (hw.comp measurable_snd).mul ((hF.comp measurable_swap).enorm)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ v in s, (∫⁻ ω, w v * ‖F v ω‖ₑ ∂P)
      ≤ ∫⁻ v in s, ENNReal.ofReal C * w v := by
        refine setLIntegral_mono' hs (fun v hv => ?_)
        rw [lintegral_const_mul _ ((hF.of_uncurry_left (x := v)).enorm)]
        calc w v * ∫⁻ ω, ‖F v ω‖ₑ ∂P ≤ w v * ENNReal.ofReal C := by gcongr; exact hb v (hsH hv)
          _ = ENNReal.ofReal C * w v := mul_comm _ _
    _ = ENNReal.ofReal C * ∫⁻ v in s, w v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The exponential weight integrates to `e^{-cRw}/c` on the far window. -/
theorem u12_exp_lintegral {c a Rw H : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hRw : 0 ≤ Rw) (hH : a < H) :
    ∫⁻ v in Set.Ioc 0 H ∩ Set.Iio (max (a - Rw) 0), ENNReal.ofReal (Real.exp (-c * (a - v))) ≤
      ENNReal.ofReal (Real.exp (-c * Rw) / c) := by
  rcases le_or_gt (max (a - Rw) 0) 0 with hb | hb
  · have : Set.Ioc 0 H ∩ Set.Iio (max (a - Rw) 0) = ∅ := by
      refine Set.eq_empty_of_forall_notMem (fun v hv => ?_)
      obtain ⟨⟨h1, h2⟩, h3⟩ := hv
      have h4 : v < max (a - Rw) 0 := h3
      linarith
    rw [this]
    simp
  · have hb' : max (a - Rw) 0 = a - Rw := by
      rcases max_cases (a - Rw) 0 with h | h
      · exact h.1
      · exfalso; linarith [h.1, h.2]
    set b := max (a - Rw) 0 with hbdef
    have hbpos : 0 < b := hb
    have hba : b ≤ a := by rw [hb']; linarith
    have hsub : Set.Ioc 0 H ∩ Set.Iio b ⊆ Set.Ioc 0 b := fun v hv => ⟨hv.1.1, (Set.mem_Iio.1 hv.2).le⟩
    calc ∫⁻ v in Set.Ioc 0 H ∩ Set.Iio b, ENNReal.ofReal (Real.exp (-c * (a - v)))
        ≤ ∫⁻ v in Set.Ioc 0 b, ENNReal.ofReal (Real.exp (-c * (a - v))) := lintegral_mono_set hsub
      _ = ENNReal.ofReal (∫ v in Set.Ioc 0 b, Real.exp (-c * (a - v))) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (Continuous.integrableOn_Ioc (by fun_prop))
        · exact Filter.Eventually.of_forall fun v => (Real.exp_pos _).le
      _ ≤ ENNReal.ofReal (Real.exp (-c * Rw) / c) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← intervalIntegral.integral_of_le hbpos.le]
        have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) b, HasDerivAt (fun v => Real.exp (-c * (a - v)) / c)
            (Real.exp (-c * (a - x))) x := by
          intro x _
          have h1 : HasDerivAt (fun v : ℝ => -c * (a - v)) c x := by
            have := ((hasDerivAt_id x).const_sub a).const_mul (-c)
            simpa using this
          have h2 := (h1.exp).div_const c
          convert h2 using 1
          field_simp
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          ((Continuous.intervalIntegrable (by fun_prop) _ _))]
        have hab : a - b = Rw := by rw [hb']; ring
        rw [hab]
        have : Real.exp (-c * (a - 0)) / c ≥ 0 := by positivity
        have h3 : Real.exp (-c * Rw) / c - Real.exp (-c * (a - 0)) / c ≤ Real.exp (-c * Rw) / c := by linarith
        simpa using h3

/-- The final bound of the far estimate. -/
theorem u12_final_bound {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → ℝ) (F : ℝ → Ω → E)
    (hF : Measurable (Function.uncurry F)) (H a Rw c K Cm : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hCm : 0 ≤ Cm)
    (ha : 0 ≤ a) (hRw : 0 ≤ Rw) (hH : a < H)
    (hb : ∀ v ∈ Set.Icc (0 : ℝ) H, ∫⁻ ω, ‖F v ω‖ₑ ∂P ≤ ENNReal.ofReal Cm)
    (hpt : ∀ᵐ ω ∂P, ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ < ∞ →
      |g ω| ≤ K * ∫ v in Set.Ioc 0 H ∩ Set.Iio (max (a - Rw) 0), Real.exp (-c * (a - v)) * ‖F v ω‖) :
    |∫ ω, g ω ∂P| ≤ K * Cm * (Real.exp (-c * Rw) / c) := by
  set b := max (a - Rw) 0 with hbdef
  have hba : b ≤ a := max_le (by linarith) ha
  set S0 : Set ℝ := Set.Ioc 0 H ∩ Set.Iio b with hS0
  have hS0m : MeasurableSet S0 := measurableSet_Ioc.inter measurableSet_Iio
  have hS0H : S0 ⊆ Set.Icc 0 H := fun v hv => ⟨hv.1.1.le, hv.1.2⟩
  have hFm : ∀ ω, Measurable (fun v => F v ω) := fun ω => hF.comp (measurable_id.prodMk measurable_const)
  -- the two Tonelli bounds
  have hw : Measurable (fun v : ℝ => ENNReal.ofReal (Real.exp (-c * (a - v)))) := by fun_prop
  have T1 := u12_tonelli P F hF H Cm hb _ hw S0 hS0m hS0H
  have hone : ∀ v : ℝ, Measurable (fun _ : ℝ => (1 : ℝ≥0∞)) := fun _ => measurable_const
  have T2 := u12_tonelli P F hF H Cm hb (fun _ => 1) measurable_const (Set.Icc 0 H) measurableSet_Icc le_rfl
  simp only [one_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at T2
  have hmeasAll : Measurable (fun ω => ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ ∂volume) := by
    have : Measurable (fun p : Ω × ℝ => ‖F p.2 p.1‖ₑ) := (hF.comp measurable_swap).enorm
    exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) H))
  have hfinAll : ∀ᵐ ω ∂P, ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ < ∞ := by
    refine ae_lt_top hmeasAll ?_
    refine ne_top_of_le_ne_top ?_ T2
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  set L : Ω → ℝ≥0∞ := fun ω => ∫⁻ v in S0, ENNReal.ofReal (Real.exp (-c * (a - v))) * ‖F v ω‖ₑ with hL
  have hLle : ∀ ω, L ω ≤ ∫⁻ v in Set.Icc (0 : ℝ) H, ‖F v ω‖ₑ := by
    intro ω
    calc L ω ≤ ∫⁻ v in S0, ‖F v ω‖ₑ := by
          refine setLIntegral_mono' hS0m (fun v hv => ?_)
          have : ENNReal.ofReal (Real.exp (-c * (a - v))) ≤ 1 := by
            rw [ENNReal.ofReal_le_one]
            exact u12_exp_le_one hc (((Set.mem_Iio.1 hv.2).le).trans hba)
          calc _ ≤ 1 * ‖F v ω‖ₑ := by gcongr
            _ = _ := one_mul _
      _ ≤ _ := lintegral_mono_set hS0H
  -- pointwise bound on the enorm
  have hptw : ∀ᵐ ω ∂P, ‖g ω‖ₑ ≤ ENNReal.ofReal K * L ω := by
    filter_upwards [hpt, hfinAll] with ω h1 h2
    have h3 := h1 h2
    have hLfin : L ω < ∞ := lt_of_le_of_lt (hLle ω) h2
    have hint : ∫ v in S0, Real.exp (-c * (a - v)) * ‖F v ω‖ = (L ω).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        (((by fun_prop : Continuous fun v : ℝ => Real.exp (-c * (a - v))).measurable.mul
          (hFm ω).norm).aestronglyMeasurable)]
      congr 1
      refine lintegral_congr fun v => ?_
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm_eq_enorm]
    rw [hint] at h3
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    calc ENNReal.ofReal |g ω| ≤ ENNReal.ofReal (K * (L ω).toReal) := ENNReal.ofReal_le_ofReal h3
      _ = ENNReal.ofReal K * L ω := by
        rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hLfin.ne]
  have hexp := u12_exp_lintegral (c := c) (a := a) (Rw := Rw) (H := H) hc ha hRw hH
  have hint2 : ∫⁻ ω, ‖g ω‖ₑ ∂P ≤ ENNReal.ofReal (K * Cm * (Real.exp (-c * Rw) / c)) := by
    calc ∫⁻ ω, ‖g ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal K * L ω ∂P := lintegral_mono_ae hptw
      _ = ENNReal.ofReal K * ∫⁻ ω, L ω ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal Cm * ∫⁻ v in S0, ENNReal.ofReal (Real.exp (-c * (a - v)))) := by
          gcongr
      _ ≤ ENNReal.ofReal K * (ENNReal.ofReal Cm * ENNReal.ofReal (Real.exp (-c * Rw) / c)) := by gcongr
      _ = ENNReal.ofReal (K * Cm * (Real.exp (-c * Rw) / c)) := by
          rw [← ENNReal.ofReal_mul hCm, ← ENNReal.ofReal_mul hK, mul_assoc]
  have hnn : 0 ≤ K * Cm * (Real.exp (-c * Rw) / c) := by positivity
  have := norm_integral_le_lintegral_norm (μ := P) g
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  refine ENNReal.toReal_le_of_le_ofReal hnn ?_
  simpa only [ofReal_norm_eq_enorm] using hint2

end HRS.MC.E213U12

end
