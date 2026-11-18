import HRS.MS.GenPathAux4

/-!
# S10.4 packet E0: weights `θ_b`, the weighted moment core and the window trace moment

* `s104_moment_core_gen`: `s56_moment_core` for an arbitrary finite measure on the time axis (hypotheses almost everywhere).
* `s104_moment_core_w`: the version with a weight `w(r) ≥ 0` on `[0,L]`.
* `s104_theta2`: `θ_b(r)^2` (`e^{-2c(b-r)}` for `r<b`, `1` for `r ≥ b`) and `∫_0^{b+T} θ_b^2 ≤ T + 1/(2c)`.
* `s104_trace_moment_w`: the window trace moment with the infimum over the cutoff radius `R`
  (`generalLocalizationRate`), in the shape needed by `r2_window_errors` (a).
Helper names carry the prefix `s104_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2WinErr

open HRS.MS.GenPath HRS.Whole

theorem s104_moment_core_gen {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μT : Measure ℝ) [IsFiniteMeasure μT] {T : ℝ} (hT : 0 ≤ T) (hμuniv : μT Set.univ = ENNReal.ofReal T)
    (en mm : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod μT))
    (hmm : AEMeasurable (fun p : Ω × ℝ => mm p.1 p.2) (P.prod μT))
    {E₁ : ℝ≥0∞} (hE₁ : E₁ ≠ ⊤) (hE : ∀ᵐ r ∂μT, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E₁)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hM : ∀ᵐ r ∂μT, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ≤ ENNReal.ofReal M₂)
    (hmm0 : ∀ ζ r, 0 ≤ mm ζ r) {c a n R2 : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hn : 0 ≤ n) (hR2 : 0 ≤ R2)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ᵐ ζ ∂P, ∀ᵐ r ∂μT,
      f ζ r ≤ ENNReal.ofReal (c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2))) :
    ∫⁻ ζ, (∫⁻ r, f ζ r ∂μT) ∂P ≤
      ENNReal.ofReal (c * T * (a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2)) := by
  set G : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (a * n) + ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2)) +
    ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2) + ENNReal.ofReal (M₂ * R2) with hG
  have hρuniv : (P.prod μT) Set.univ = ENNReal.ofReal T := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul, hμuniv]
  have hg1 : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.sqrt (en z.1 z.2))) (P.prod μT) :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hen).ennreal_ofReal
  have hg2 : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (mm z.1 z.2)) (P.prod μT) := hmm.ennreal_ofReal
  have hGm : AEMeasurable G (P.prod μT) := by
    refine (((aemeasurable_const.add (hg1.const_mul _)).add (hg2.const_mul _)).add aemeasurable_const)
  -- step 1: pointwise domination
  have hstep1 : ∫⁻ ζ, (∫⁻ r, f ζ r ∂μT) ∂P ≤
      ∫⁻ ζ, (∫⁻ r, ENNReal.ofReal c * G (ζ, r) ∂μT) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hf] with ζ hζ
    refine lintegral_mono_ae ?_
    filter_upwards [hζ] with r hr
    refine hr.trans (le_of_eq ?_)
    simp only [hG]
    have hs : 0 ≤ Real.sqrt (en ζ r) := Real.sqrt_nonneg _
    have hm : 0 ≤ mm ζ r := hmm0 ζ r
    have hsum : ENNReal.ofReal (a * n) + ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en ζ r)) +
        ENNReal.ofReal R2 * ENNReal.ofReal (mm ζ r) + ENNReal.ofReal (M₂ * R2) =
        ENNReal.ofReal (a * n + a * Real.sqrt (en ζ r) + R2 * mm ζ r + M₂ * R2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul ha (q := Real.sqrt (en ζ r)), ENNReal.ofReal_mul hR2 (q := mm ζ r)]
    have e : c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2) =
        c * (a * n + a * Real.sqrt (en ζ r) + R2 * mm ζ r + M₂ * R2) := by ring
    rw [e, ENNReal.ofReal_mul hc, hsum]
  refine hstep1.trans ?_
  set ρ : Measure (Ω × ℝ) := P.prod μT with hρ
  -- step 2: pull out the constant and pass to the product measure
  have h2 : ∫⁻ ζ, (∫⁻ r, ENNReal.ofReal c * G (ζ, r) ∂μT) ∂P =
      ENNReal.ofReal c * ∫⁻ z, G z ∂ρ := by
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [hρ, lintegral_prod _ hGm]
  rw [h2]
  -- step 3: the three integrals
  have hpt : ∀ᵐ r ∂μT, ∫⁻ ζ, ENNReal.ofReal (Real.sqrt (en ζ r)) ^ (2 : ℝ) ∂P ≤ E₁ := by
    filter_upwards [hE] with r hr
    refine le_trans (lintegral_mono fun ζ => ?_) hr
    by_cases h : 0 ≤ en ζ r
    · rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero_of_nonpos (not_le.1 h).le]
      simp
  have hint1 : ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ∂ρ ≤
      ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ) := by
    refine (s56_lintegral_le_sqrt' ρ hg1).trans ?_
    rw [hρuniv]
    have hsw : ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ^ (2 : ℝ) ∂ρ ≤ E₁ * ENNReal.ofReal T := by
      rw [hρ, lintegral_prod_symm _ (hg1.pow_const _)]
      simp only
      calc ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (Real.sqrt (en ζ r)) ^ (2 : ℝ) ∂P ∂μT
          ≤ ∫⁻ r, E₁ ∂μT := by
            exact lintegral_mono_ae hpt
        _ = E₁ * ENNReal.ofReal T := by rw [lintegral_const, hμuniv]
    calc ENNReal.ofReal T ^ (1 / 2 : ℝ) * (∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal T ^ (1 / 2 : ℝ) * (E₁ * ENNReal.ofReal T) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          have : ENNReal.ofReal T ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ) = ENNReal.ofReal T := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num
          calc ENNReal.ofReal T ^ (1 / 2 : ℝ) * (E₁ ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ))
              = (ENNReal.ofReal T ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ)) * E₁ ^ (1 / 2 : ℝ) := by ring
            _ = _ := by rw [this]
  have hint2 : ∫⁻ z, ENNReal.ofReal (mm z.1 z.2) ∂ρ ≤ ENNReal.ofReal M₂ * ENNReal.ofReal T := by
    rw [hρ, lintegral_prod_symm _ hg2]
    simp only
    calc ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ∂μT ≤ ∫⁻ r, ENNReal.ofReal M₂ ∂μT := by
          exact lintegral_mono_ae hM
      _ = ENNReal.ofReal M₂ * ENNReal.ofReal T := by rw [lintegral_const, hμuniv]
  have hGint : ∫⁻ z, G z ∂ρ =
      ENNReal.ofReal (a * n) * ENNReal.ofReal T + ENNReal.ofReal a * ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ∂ρ +
      ENNReal.ofReal R2 * ∫⁻ z, ENNReal.ofReal (mm z.1 z.2) ∂ρ + ENNReal.ofReal (M₂ * R2) * ENNReal.ofReal T := by
    simp only [hG]
    have hA : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (a * n) +
        ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2)) +
        ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2)) ρ :=
      (aemeasurable_const.add (hg1.const_mul _)).add (hg2.const_mul _)
    have hB : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (a * n) +
        ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2))) ρ :=
      aemeasurable_const.add (hg1.const_mul _)
    rw [lintegral_add_left' hA (fun _ => ENNReal.ofReal (M₂ * R2)), lintegral_add_left' hB
      (fun z : Ω × ℝ => ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2)),
      lintegral_add_left' (aemeasurable_const (b := ENNReal.ofReal (a * n)))
        (fun z : Ω × ℝ => ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2))),
      lintegral_const, lintegral_const, lintegral_const_mul'' _ hg1, lintegral_const_mul'' _ hg2, hρuniv]
  have hbound : ∫⁻ z, G z ∂ρ ≤ ENNReal.ofReal (a * n) * ENNReal.ofReal T +
      ENNReal.ofReal a * (ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal R2 * (ENNReal.ofReal M₂ * ENNReal.ofReal T) + ENNReal.ofReal (M₂ * R2) * ENNReal.ofReal T := by
    rw [hGint]
    gcongr
  have hE₁r : E₁ ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt E₁.toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hE₁]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), Real.sqrt_eq_rpow]
  rw [hE₁r] at hbound
  have hse : 0 ≤ Real.sqrt E₁.toReal := Real.sqrt_nonneg _
  refine (mul_le_mul' le_rfl hbound).trans (le_of_eq ?_)
  have e1 : c * T * (a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2) =
      c * (a * n * T + a * (T * Real.sqrt E₁.toReal) + R2 * (M₂ * T) + M₂ * R2 * T) := by ring
  rw [e1, ENNReal.ofReal_mul hc, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity : 0 ≤ a * n), ENNReal.ofReal_mul ha (q := T * Real.sqrt E₁.toReal),
    ENNReal.ofReal_mul hT (q := Real.sqrt E₁.toReal), ENNReal.ofReal_mul hR2 (q := M₂ * T),
    ENNReal.ofReal_mul hM₂ (q := T), ENNReal.ofReal_mul (by positivity : 0 ≤ M₂ * R2) (q := T)]



/-- The weighted moment core: weight `w(r) ≥ 0` on `[0,L]` with `∫_0^L w ≤ W`. -/
theorem s104_moment_core_w {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {L : ℝ} (w : ℝ → ℝ) (hw : Measurable w) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ r in Set.Icc (0 : ℝ) L, ENNReal.ofReal (w r) ≤ ENNReal.ofReal W)
    (en mm : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 L))))
    (hmm : AEMeasurable (fun p : Ω × ℝ => mm p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 L))))
    {E₁ : ℝ≥0∞} (hE₁ : E₁ ≠ ⊤) (hE : ∀ r ∈ Set.Icc (0 : ℝ) L, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E₁)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) L, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ≤ ENNReal.ofReal M₂)
    (hmm0 : ∀ ζ r, 0 ≤ mm ζ r) {c a n R2 : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hn : 0 ≤ n) (hR2 : 0 ≤ R2)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) L, f ζ r ≤ ENNReal.ofReal (w r) *
      ENNReal.ofReal (c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2))) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) L, f ζ r) ∂P ≤
      ENNReal.ofReal (c * W * (a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2)) := by
  set μ0 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) L) with hμ0
  set ν : Measure ℝ := μ0.withDensity (fun r => ENNReal.ofReal (w r)) with hν
  have hνuniv' : ν Set.univ = ∫⁻ r in Set.Icc (0 : ℝ) L, ENNReal.ofReal (w r) := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hνle : ν Set.univ ≤ ENNReal.ofReal W := hνuniv' ▸ hW
  haveI : IsFiniteMeasure ν := ⟨lt_of_le_of_lt hνle ENNReal.ofReal_lt_top⟩
  set Wr : ℝ := (ν Set.univ).toReal with hWr
  have hWr0 : 0 ≤ Wr := ENNReal.toReal_nonneg
  have hνuniv : ν Set.univ = ENNReal.ofReal Wr := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hWrW : Wr ≤ W := ENNReal.toReal_le_of_le_ofReal hW0 hνle
  have hac : ν ≪ μ0 := withDensity_absolutelyContinuous _ _
  have hmem : ∀ᵐ r ∂ν, r ∈ Set.Icc (0 : ℝ) L := hac.ae_le (ae_restrict_mem measurableSet_Icc)
  have hacp : P.prod ν ≪ P.prod μ0 := (Measure.AbsolutelyContinuous.refl P).prod hac
  have hmeasw : Measurable (fun r => ENNReal.ofReal (w r)) := hw.ennreal_ofReal
  set g : Ω → ℝ → ℝ≥0∞ := fun ζ r =>
    ENNReal.ofReal (c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2)) with hg
  have hstep : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) L, f ζ r) ∂P ≤ ∫⁻ ζ, (∫⁻ r, g ζ r ∂ν) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hf] with ζ hζ
    rw [hν, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeasw
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    exact setLIntegral_mono' measurableSet_Icc fun r hr => hζ r hr
  refine hstep.trans ?_
  have hcore := s104_moment_core_gen P ν hWr0 hνuniv en mm (hen.mono_ac hacp) (hmm.mono_ac hacp) hE₁
    (hmem.mono fun r hr => hE r hr) hM₂ (hmem.mono fun r hr => hM r hr) hmm0 hc ha hn hR2 g
    (Eventually.of_forall fun ζ => Eventually.of_forall fun r => le_rfl)
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK : 0 ≤ a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2 := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWrW hc) hK
  linarith

/-- The squared window weight `θ_b(r)^2`. -/
def s104_theta2 (c b r : ℝ) : ℝ := if r < b then Real.exp (-2 * c * (b - r)) else 1

lemma s104_theta2_pos (c b r : ℝ) : 0 < s104_theta2 c b r := by
  unfold s104_theta2; split_ifs
  · exact Real.exp_pos _
  · exact one_pos

lemma s104_theta2_le_one {c : ℝ} (hc : 0 ≤ c) (b r : ℝ) : s104_theta2 c b r ≤ 1 := by
  unfold s104_theta2; split_ifs with h
  · rw [Real.exp_le_one_iff]
    have : 0 ≤ b - r := by linarith
    nlinarith
  · exact le_rfl

lemma s104_theta2_measurable (c b : ℝ) : Measurable (s104_theta2 c b) := by
  unfold s104_theta2
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

lemma s104_theta2_le_exp {c : ℝ} (hc : 0 ≤ c) (b : ℝ) {r : ℝ} (hr : r ≤ b) :
    s104_theta2 c b r ≤ Real.exp (-2 * c * (b - r)) := by
  unfold s104_theta2; split_ifs with h
  · exact le_rfl
  · have : r = b := le_antisymm hr (not_lt.1 h)
    subst this; simp

lemma s104_exp_integral {c : ℝ} (hc : 0 < c) {b : ℝ} (hb : 0 ≤ b) :
    ∫ r in Set.Icc (0 : ℝ) b, Real.exp (-2 * c * (b - r)) ≤ 1 / (2 * c) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) b, HasDerivAt (fun r => Real.exp (-2 * c * (b - r)) / (2 * c))
      (Real.exp (-2 * c * (b - x))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -2 * c * (b - r)) (2 * c) x := by
      have := ((hasDerivAt_id x).const_sub b).const_mul (-2 * c)
      simpa using this
    have h2 := (h1.exp).div_const (2 * c)
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Continuous.intervalIntegrable (by fun_prop) _ _))]
  have : Real.exp (-2 * c * (b - b)) = 1 := by simp
  rw [this]
  have h3 : 0 < Real.exp (-2 * c * (b - 0)) := Real.exp_pos _
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

theorem s104_theta2_lintegral {c : ℝ} (hc : 0 < c) {b T : ℝ} (hb : 0 ≤ b) (hT : 0 ≤ T) :
    ∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (s104_theta2 c b r) ≤
      ENNReal.ofReal (1 / (2 * c) + T) := by
  rw [← Set.Icc_union_Icc_eq_Icc hb (by linarith : b ≤ b + T)]
  refine (lintegral_union_le _ _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) hT]
  refine add_le_add ?_ ?_
  · calc ∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal (s104_theta2 c b r)
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) b, ENNReal.ofReal (Real.exp (-2 * c * (b - r))) :=
          setLIntegral_mono' measurableSet_Icc fun r hr =>
            ENNReal.ofReal_le_ofReal (s104_theta2_le_exp hc.le b hr.2)
      _ = ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) b, Real.exp (-2 * c * (b - r))) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · exact (Continuous.integrableOn_Icc (by fun_prop))
          · exact Eventually.of_forall fun r => (Real.exp_pos _).le
      _ ≤ _ := ENNReal.ofReal_le_ofReal (s104_exp_integral hc hb)
  · calc ∫⁻ r in Set.Icc b (b + T), ENNReal.ofReal (s104_theta2 c b r)
        ≤ ∫⁻ r in Set.Icc b (b + T), 1 :=
          setLIntegral_mono' measurableSet_Icc fun r _ => by
            simpa using s104_theta2_le_one hc.le b r
      _ = ENNReal.ofReal T := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Icc]
          simp

/-- The window trace moment with the infimum over the cutoff radius `R`. -/
theorem s104_trace_moment_w {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d N : ℕ) {L : ℝ} (w : ℝ → ℝ) (hw : Measurable w) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ r in Set.Icc (0 : ℝ) L, ENNReal.ofReal (w r) ≤ ENNReal.ofReal W)
    (en mm : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 L))))
    (hmm : AEMeasurable (fun p : Ω × ℝ => mm p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 L))))
    {E₁ : ℝ≥0∞} (hE₁ : E₁ ≠ ⊤) (hE : ∀ r ∈ Set.Icc (0 : ℝ) L, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E₁)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) L, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ≤ ENNReal.ofReal M₂)
    (hmm0 : ∀ ζ r, 0 ≤ mm ζ r) {c : ℝ} (hc : 0 ≤ c)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) L, ∀ R : ℝ, 1 ≤ R → f ζ r ≤ ENNReal.ofReal (w r) *
      ENNReal.ofReal (c * (R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (en ζ r)) +
        (mm ζ r + M₂) * (1 / R ^ 2)))) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) L, f ζ r) ∂P ≤
      ENNReal.ofReal (2 * c * W * generalLocalizationRate d E₁.toReal M₂ N) := by
  have hR : ∀ R : {R : ℝ // 1 ≤ R}, ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) L, f ζ r) ∂P ≤
      ENNReal.ofReal (2 * c * W * (R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) +
        Real.sqrt E₁.toReal) + (1 + M₂) * R.1 ^ (-(2 : ℝ)))) := by
    intro R
    have hRpos : 0 < R.1 := by linarith [R.2]
    have hcore := s104_moment_core_w P w hw hW0 hW en mm hen hmm hE₁ hE hM₂ hM hmm0
      (c := c) (a := R.1 ^ ((d : ℝ) / 2)) (n := (N : ℝ) ^ (-(1 / (d : ℝ)))) (R2 := 1 / R.1 ^ 2)
      hc (by positivity) (by positivity) (by positivity) f
      (hf.mono fun ζ h r hr => h r hr R.1 R.2)
    refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrneg : R.1 ^ (-(2 : ℝ)) = 1 / R.1 ^ 2 := by
      rw [Real.rpow_neg hRpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
    rw [hrneg]
    have h1' : 0 ≤ c * W := by positivity
    have h2' : 0 ≤ R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E₁.toReal) := by
      positivity
    have h3' : 0 ≤ M₂ * (1 / R.1 ^ 2) := by positivity
    have hR2 : 0 ≤ 1 / R.1 ^ 2 := by positivity
    nlinarith [mul_nonneg h1' h2', mul_nonneg h1' h3', mul_nonneg h1' hR2]
  have := s56_le_iInf (K := 2 * c * W) (by positivity) (fun R : {R : ℝ // 1 ≤ R} =>
    R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E₁.toReal) +
      (1 + M₂) * R.1 ^ (-(2 : ℝ))) (fun R : {R : ℝ // 1 ≤ R} => by
      have : 0 < R.1 := by linarith [R.2]
      positivity) hR
  refine this.trans (le_of_eq ?_)
  unfold generalLocalizationRate
  rfl

end HRS.MS.R2WinErr
