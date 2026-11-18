import HRS.Main.ThermLin2E1a

/-!
# THERMLIN2 E1b: the pathwise bound `Bm` of the remainder and its second moment

`tl2E1_Bm` is the random variable `Bm ω = C K ∫_0^{a+T} e^{-c max(a-r,0)} e^{-κ r} ‖Zw^r(ω)‖_{E_{m-a₀}} dr` of the plan
(`Zw` clamped to `[0,a+T]` so that the integrand is jointly measurable).  No plan statement is used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- The time-clamped process. -/
def tl2E1_clamp (a T : ℝ) {Ω : Type*} {m : ℝ} (Z : ℝ → Ω → NegSobolev d m) (r : ℝ) (ω : Ω) : NegSobolev d m :=
  Z (max 0 (min r (a + T))) ω

/-- The random bound of the remainder. -/
def tl2E1_Bm (m b a T c₀ κ CK : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal CK * ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
    ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) *
      tl2NormShift m b (tl2E1_clamp a T Z r ω)

lemma tl2E1_clamp_eq {a T : ℝ} (ha : 0 ≤ a) (hT : 0 < T) {Ω : Type*} {m : ℝ} (Z : ℝ → Ω → NegSobolev d m) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) (a + T)) (ω : Ω) : tl2E1_clamp a T Z r ω = Z r ω := by
  unfold tl2E1_clamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

lemma tl2E1_clamp_uncurry_measurable {a T : ℝ} (h0 : 0 ≤ a + T) {Ω : Type*} [MeasurableSpace Ω] {m : ℝ}
    (Z : ℝ → Ω → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ ω, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) :
    Measurable (Function.uncurry (tl2E1_clamp a T Z)) := by
  refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun r => hZm _)
  have hmem : ∀ r : ℝ, max 0 (min r (a + T)) ∈ Set.Icc (0 : ℝ) (a + T) := by
    intro r
    exact ⟨le_max_left _ _, max_le h0 (min_le_right _ _)⟩
  exact (hZc ω).comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hmem

lemma tl2E1_Bm_measurable (m b a T c₀ κ CK : ℝ) (h0 : 0 ≤ a + T) {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → Ω → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ ω, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) :
    Measurable (tl2E1_Bm m b a T c₀ κ CK Z) := by
  have hcl := tl2E1_clamp_uncurry_measurable h0 Z hZm hZc
  have hF : Measurable fun q : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (-c₀ * max (a - q.2) 0) * Real.exp (-κ * q.2)) *
        tl2NormShift m b (tl2E1_clamp a T Z q.2 q.1) := by
    refine Measurable.mul ?_ ((tl2E1_normShift_measurable m b).comp (hcl.comp (measurable_snd.prodMk measurable_fst)))
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  exact (hF.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) (a + T)))).const_mul _

lemma tl2E1_Bm_sq {m b a T c₀ κ CK M Cφ cφ : ℝ} (hCK : 0 ≤ CK) (hM : 0 ≤ M) (hCφ : 0 ≤ Cφ) (h0 : 0 ≤ a + T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ ω, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) (ha : 0 ≤ a) (hT : 0 < T)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∫⁻ ω, tl2NormShift m b (Z r ω) ^ 2 ∂P ≤ ENNReal.ofReal M)
    (hφ : ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) ≤
        ENNReal.ofReal (Cφ * Real.exp (-cφ * a))) :
    ∫⁻ ω, tl2E1_Bm m b a T c₀ κ CK Z ω ^ 2 ∂P ≤
      ENNReal.ofReal (CK * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M) ^ 2 := by
  have hcl := tl2E1_clamp_uncurry_measurable h0 Z hZm hZc
  have hN : Measurable (Function.uncurry fun r ω => tl2NormShift m b (tl2E1_clamp a T Z r ω)) :=
    (tl2E1_normShift_measurable m b).comp hcl
  have hN' : Measurable fun q : Ω × ℝ => tl2NormShift m b (tl2E1_clamp a T Z q.2 q.1) :=
    (tl2E1_normShift_measurable m b).comp (hcl.comp (measurable_snd.prodMk measurable_fst))
  have hg : Measurable fun r : ℝ => ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have hw := tl2E1_wcs P (measurableSet_Icc (a := (0 : ℝ)) (b := a + T)) hg hN (M := ENNReal.ofReal M)
    (fun r hr => by
      have := hmom r hr
      simpa only [tl2E1_clamp_eq ha hT Z hr] using this)
  have hsq : ∀ ω, tl2E1_Bm m b a T c₀ κ CK Z ω ^ 2 = ENNReal.ofReal CK ^ 2 *
      (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) *
          tl2NormShift m b (tl2E1_clamp a T Z r ω)) ^ 2 := by
    intro ω
    unfold tl2E1_Bm
    rw [mul_pow]
  simp_rw [hsq]
  have hI : Measurable fun ω => (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) *
          tl2NormShift m b (tl2E1_clamp a T Z r ω)) ^ 2 := by
    have hF : Measurable fun q : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (-c₀ * max (a - q.2) 0) * Real.exp (-κ * q.2)) *
          tl2NormShift m b (tl2E1_clamp a T Z q.2 q.1) :=
      (hg.comp measurable_snd).mul hN'
    exact (hF.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) (a + T)))).pow_const 2
  rw [lintegral_const_mul _ hI]
  calc ENNReal.ofReal CK ^ 2 * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) *
          tl2NormShift m b (tl2E1_clamp a T Z r ω)) ^ 2 ∂P
      ≤ ENNReal.ofReal CK ^ 2 * ((∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r))) ^ 2 * ENNReal.ofReal M) :=
        mul_le_mul' le_rfl hw
    _ ≤ ENNReal.ofReal CK ^ 2 * (ENNReal.ofReal (Cφ * Real.exp (-cφ * a)) ^ 2 * ENNReal.ofReal M) := by
        gcongr
    _ = ENNReal.ofReal (CK * (Cφ * Real.exp (-cφ * a)) * Real.sqrt M) ^ 2 := by
        have hY : 0 ≤ Cφ * Real.exp (-cφ * a) := mul_nonneg hCφ (Real.exp_pos _).le
        rw [ENNReal.ofReal_mul (mul_nonneg hCK hY), ENNReal.ofReal_mul hCK, mul_pow, mul_pow,
          ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hM]
        ring

/-- The pathwise remainder bound at time `t ∈ [a,a+T]` is dominated by `Bm`. -/
lemma tl2E1_Bm_ge {m b a T c₀ κ CK : ℝ} (hCK : 0 ≤ CK) (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Set.Icc a (a + T)) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω) :
    ENNReal.ofReal CK * ∫⁻ r in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.exp (-c₀ * (t - r)) * Real.exp (-κ * r)) * tl2NormShift m b (Z r ω) ≤
      tl2E1_Bm m b a T c₀ κ CK Z ω := by
  unfold tl2E1_Bm
  refine mul_le_mul' le_rfl ?_
  calc ∫⁻ r in Set.Icc (0 : ℝ) t,
        ENNReal.ofReal (Real.exp (-c₀ * (t - r)) * Real.exp (-κ * r)) * tl2NormShift m b (Z r ω)
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (-c₀ * max (a - r) 0) * Real.exp (-κ * r)) *
          tl2NormShift m b (tl2E1_clamp a T Z r ω) := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        have hr' : r ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hr.1, hr.2.trans ht.2⟩
        rw [tl2E1_clamp_eq ha hT Z hr']
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
        have : max (a - r) 0 ≤ t - r := max_le (by linarith [ht.1]) (by linarith [hr.2])
        nlinarith
    _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)

end HRS.ThermLin.Plan2
