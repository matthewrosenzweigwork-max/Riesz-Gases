import HRS.Sections.AdjKSpec

/-!
# ADJKC Aux3: packet C3 (deterministic convolution `L²` bound), helpers
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjKC

/-- Cauchy-Schwarz in `ℝ≥0∞`: `(∫ f)² ≤ ν(univ) ∫ f²`. -/
theorem adjkc_cs {α : Type*} [MeasurableSpace α] (ν : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν) ^ 2 ≤ ν univ * ∫⁻ x, f x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := f) aemeasurable_const hf
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    mul_one] at h
  have h2 : (∫⁻ x, f x ∂ν) ^ 2 ≤ ((ν univ) ^ (1 / (2 : ℝ)) * (∫⁻ a, f a ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
    pow_le_pow_left' h 2
  have e : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, e, e]
  congr 1
  refine lintegral_congr fun x => ?_
  exact ENNReal.rpow_two (f x)

/-- The exponential weight `w(r) = e^{-c(a-r)}` for `r ≤ a`, `1` for `r > a`. -/
def adjkcW (c a : ℝ) (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (if r ≤ a then Real.exp (-c * (a - r)) else 1)

theorem adjkcW_measurable (c a : ℝ) : Measurable (adjkcW c a) := by
  unfold adjkcW
  refine ENNReal.measurable_ofReal.comp (Measurable.ite measurableSet_Iic ?_ measurable_const)
  fun_prop

theorem adjkcW_ne_top (c a r : ℝ) : adjkcW c a r ≠ ⊤ := ENNReal.ofReal_ne_top

theorem adjkc_W_integral {c : ℝ} (hc : 0 < c) {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 < T) :
    ∫⁻ r in Set.Ioc 0 (a + T), adjkcW c a r ≤ ENNReal.ofReal (1 / c + T) := by
  have hsplit : Set.Ioc (0 : ℝ) (a + T) = Set.Ioc 0 a ∪ Set.Ioc a (a + T) :=
    (Set.Ioc_union_Ioc_eq_Ioc ha (by linarith)).symm
  rw [hsplit, lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  have h1 : ∫⁻ r in Set.Ioc 0 a, adjkcW c a r = ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (Real.exp (-c * (a - r))) := by
    refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    unfold adjkcW; rw [if_pos hr.2]
  have h2 : ∫⁻ r in Set.Ioc a (a + T), adjkcW c a r = ENNReal.ofReal T := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1) fun r hr => by
      unfold adjkcW; rw [if_neg (not_le.2 hr.1)]; simp]
    simp
  rw [h1, h2]
  have hcont : Continuous fun r : ℝ => Real.exp (-c * (a - r)) := by fun_prop
  have hint : IntervalIntegrable (fun r : ℝ => Real.exp (-c * (a - r))) volume 0 a :=
    hcont.intervalIntegrable _ _
  have hI : ∫ r in (0 : ℝ)..a, Real.exp (-c * (a - r)) ≤ 1 / c := by
    have hd : ∀ r ∈ Set.uIcc (0 : ℝ) a, HasDerivAt (fun r : ℝ => Real.exp (-c * (a - r)) / c)
        (Real.exp (-c * (a - r))) r := by
      intro r _
      have h1 : HasDerivAt (fun r : ℝ => -c * (a - r)) c r := by
        have := ((hasDerivAt_id' r).const_sub a).const_mul (-c)
        convert this using 1; ring
      have h2 := (h1.exp).div_const c
      convert h2 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp only [sub_zero, sub_self, mul_zero, Real.exp_zero]
    have : 0 ≤ Real.exp (-c * a) / c := by positivity
    have e1 : (1 : ℝ) / c = 1 / c := rfl
    linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) a)] fun r => Real.exp (-c * (a - r)) :=
    Eventually.of_forall fun r => (Real.exp_pos _).le
  have hlint : ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (Real.exp (-c * (a - r))) =
      ENNReal.ofReal (∫ r in Set.Ioc 0 a, Real.exp (-c * (a - r))) :=
    (ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Ioc) hnn).symm
  rw [hlint, ← intervalIntegral.integral_of_le ha, ← ENNReal.ofReal_add]
  · exact ENNReal.ofReal_le_ofReal (by linarith)
  · exact (intervalIntegral.integral_nonneg ha fun r _ => (Real.exp_pos _).le)
  · exact hT.le


open HRS.AdjK in
theorem adjkc_det_convolution_L2 {d : ℕ} (m : ℝ) (T CV c : ℝ) (hT : 0 < T) (hCV : 0 ≤ CV) (hc : 0 < c) :
    ∀ (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV * Real.exp (-c * (t - u))) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : ℝ → Ω → NegSobolev d m), Measurable (Function.uncurry R) → ∀ b : ℝ, 0 ≤ b →
        (∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2)) →
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, (⨆ t ∈ ratIcc a (a + T),
              ‖∫ r in (0 : ℝ)..t, Vev t r (R r ω)‖ₑ) ^ 2 ∂P ≤
            ENNReal.ofReal ((CV * (1 / c + T) * b) ^ 2) := by
  intro Vev hV Ω _ P _ R hR b hb hRb a ha
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 (a + T)) with hμ
  set ν : Measure ℝ := μ.withDensity (adjkcW c a) with hν
  have hW : ν univ ≤ ENNReal.ofReal (1 / c + T) := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact adjkc_W_integral hc ha hT
  have hWtop : ν univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hRω : ∀ ω, Measurable fun r => ‖R r ω‖ₑ := fun ω =>
    measurable_enorm.comp (hR.comp (measurable_id.prodMk measurable_const))
  have hpt : ∀ ω, (⨆ t ∈ ratIcc a (a + T), ‖∫ r in (0 : ℝ)..t, Vev t r (R r ω)‖ₑ) ≤
      ENNReal.ofReal CV * ∫⁻ r, ‖R r ω‖ₑ ∂ν := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    have ht' : t ∈ Set.Icc a (a + T) := ht.1
    rw [intervalIntegral.integral_of_le (ha.trans ht'.1)]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ r in Set.Ioc 0 t, ‖Vev t r (R r ω)‖ₑ
        ≤ ∫⁻ r in Set.Ioc 0 t, ENNReal.ofReal CV * (adjkcW c a r * ‖R r ω‖ₑ) := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          have hop := hV r t hr.1.le hr.2
          have h1 : ‖Vev t r (R r ω)‖ ≤ CV * Real.exp (-c * (t - r)) * ‖R r ω‖ :=
            ((Vev t r).le_opNorm _).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
          have h2 : CV * Real.exp (-c * (t - r)) ≤
              CV * (if r ≤ a then Real.exp (-c * (a - r)) else 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hCV
            split_ifs with hra
            · exact Real.exp_le_exp.2 (by nlinarith [ht'.1])
            · exact Real.exp_le_one_iff.2 (by nlinarith [hr.2])
          calc ‖Vev t r (R r ω)‖ₑ = ENNReal.ofReal ‖Vev t r (R r ω)‖ := (ofReal_norm_eq_enorm _).symm
            _ ≤ ENNReal.ofReal (CV * (if r ≤ a then Real.exp (-c * (a - r)) else 1) * ‖R r ω‖) :=
                ENNReal.ofReal_le_ofReal (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
            _ = ENNReal.ofReal CV * (adjkcW c a r * ‖R r ω‖ₑ) := by
                rw [ENNReal.ofReal_mul (mul_nonneg hCV (by split_ifs <;> positivity)),
                  ENNReal.ofReal_mul hCV, ofReal_norm_eq_enorm, mul_assoc]
                rfl
      _ ≤ ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal CV * (adjkcW c a r * ‖R r ω‖ₑ) :=
          lintegral_mono_set (Set.Ioc_subset_Ioc_right ht'.2)
      _ = ENNReal.ofReal CV * ∫⁻ r, ‖R r ω‖ₑ ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hν,
            lintegral_withDensity_eq_lintegral_mul _ (adjkcW_measurable c a) (hRω ω)]
          rfl
  have hcs : ∀ ω, (∫⁻ r, ‖R r ω‖ₑ ∂ν) ^ 2 ≤ ν univ * ∫⁻ r, ‖R r ω‖ₑ ^ 2 ∂ν := fun ω =>
    adjkc_cs ν (hRω ω).aemeasurable
  have hjoint : Measurable (fun p : Ω × ℝ => ‖R p.2 p.1‖ₑ ^ 2) :=
    (measurable_enorm.comp (hR.comp measurable_swap)).pow_const 2
  have hinner : Measurable (fun r : ℝ => ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P) := by
    have : Measurable (fun p : ℝ × Ω => ‖R p.1 p.2‖ₑ ^ 2) :=
      (measurable_enorm.comp hR).pow_const 2
    exact this.lintegral_prod_right'
  calc ∫⁻ ω, (⨆ t ∈ ratIcc a (a + T), ‖∫ r in (0 : ℝ)..t, Vev t r (R r ω)‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal CV ^ 2 * (ν univ * ∫⁻ r, ‖R r ω‖ₑ ^ 2 ∂ν) ∂P := by
        refine lintegral_mono fun ω => ?_
        calc _ ≤ (ENNReal.ofReal CV * ∫⁻ r, ‖R r ω‖ₑ ∂ν) ^ 2 := pow_le_pow_left' (hpt ω) 2
          _ = ENNReal.ofReal CV ^ 2 * (∫⁻ r, ‖R r ω‖ₑ ∂ν) ^ 2 := mul_pow _ _ _
          _ ≤ _ := by gcongr; exact hcs ω
    _ = ENNReal.ofReal CV ^ 2 * (ν univ * ∫⁻ ω, ∫⁻ r, ‖R r ω‖ₑ ^ 2 ∂ν ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_const_mul' _ _ hWtop]
    _ = ENNReal.ofReal CV ^ 2 * (ν univ * ∫⁻ r, ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ∂ν) := by
        rw [lintegral_lintegral_swap (hjoint.aemeasurable (μ := P.prod ν))]
    _ ≤ ENNReal.ofReal CV ^ 2 * (ν univ * (ν univ * ENNReal.ofReal (b ^ 2))) := by
        gcongr
        rw [hν, lintegral_withDensity_eq_lintegral_mul _ (adjkcW_measurable c a) hinner]
        calc ∫⁻ r, (adjkcW c a * fun r => ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P) r ∂μ
            ≤ ∫⁻ r, adjkcW c a r * ENNReal.ofReal (b ^ 2) ∂μ := by
              refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
              exact mul_le_mul_right (hRb r hr.1.le) _
          _ = ν univ * ENNReal.ofReal (b ^ 2) := by
              rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hν,
                withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ ≤ ENNReal.ofReal CV ^ 2 * (ENNReal.ofReal (1 / c + T) * (ENNReal.ofReal (1 / c + T) *
          ENNReal.ofReal (b ^ 2))) := by gcongr
    _ = ENNReal.ofReal ((CV * (1 / c + T) * b) ^ 2) := by
        have h0 : 0 ≤ 1 / c + T := by positivity
        rw [← ENNReal.ofReal_pow hCV, ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h0,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end HRS.AdjKC
