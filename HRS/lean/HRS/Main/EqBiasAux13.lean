import HRS.Main.EqBiasAux12

/-!
# EQ-BIAS, S9d: integration in the time variable against the weight `(1 - t)`
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

theorem eqbias_int_rpow {q : ℝ} (hq : -1 < q) :
    IntegrableOn (fun t : ℝ => t ^ q) (Ioc (0 : ℝ) 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, t ^ q = 1 / (q + 1) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hq
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hi, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hq)]
  have : (0 : ℝ) ^ (q + 1) = 0 := Real.zero_rpow (by linarith)
  rw [Real.one_rpow, this]
  ring

theorem eqbias_time_int {Λ n R Bc B1 κq q : ℝ} (hq : -1 < q) (hΛ : 0 ≤ Λ) (hn : 0 ≤ n) (hR : 0 ≤ R)
    (hBc : 0 ≤ Bc) (hB1 : 0 ≤ B1) (hκq : 0 ≤ κq) {v : ℝ → ℝ} {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ENNReal.ofReal D =
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * Λ) * ENNReal.ofReal (v t))
    (hv : ∀ t ∈ Ioc (0 : ℝ) 1, |v t - n * R * (κq * t ^ q)| ≤ Bc + B1 * (κq * t ^ q)) :
    |D - Λ * (n * R * κq) * (1 / ((q + 1) * (q + 2)))| ≤ Λ * (Bc + B1 * κq / (q + 1)) := by
  obtain ⟨hi1, hI1⟩ := eqbias_int_rpow hq
  obtain ⟨hi2, hI2⟩ := eqbias_int_rpow (q := q + 1) (by linarith)
  set a : ℝ → ℝ := fun t => (1 - t) * Λ * (n * R * (κq * t ^ q)) with ha
  set b : ℝ → ℝ := fun t => Λ * (Bc + B1 * (κq * t ^ q)) with hb
  have hq1 : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ t ^ q := fun t ht => Real.rpow_nonneg ht.1.le _
  have ha0 : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ a t := fun t ht => by
    have h1 : 0 ≤ 1 - t := by linarith [ht.2]
    have := hq1 t ht
    simp only [ha]; positivity
  have hb0 : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ b t := fun t ht => by
    have := hq1 t ht
    simp only [hb]; positivity
  have hbm : Measurable fun t : ℝ => ENNReal.ofReal (b t) := by
    refine ENNReal.measurable_ofReal.comp ?_
    simp only [hb]
    exact measurable_const.mul (measurable_const.add (measurable_const.mul
      (measurable_const.mul (measurable_id.pow_const q))))
  -- explicit integrals
  have hic : IntegrableOn (fun _ : ℝ => Bc) (Ioc (0 : ℝ) 1) := integrableOn_const (by simp)
  have hibt : IntegrableOn b (Ioc (0 : ℝ) 1) := by
    simp only [hb]
    exact (hic.add ((hi1.const_mul κq).const_mul B1)).const_mul Λ
  have hiat : IntegrableOn a (Ioc (0 : ℝ) 1) := by
    have : IntegrableOn (fun t : ℝ => (Λ * (n * R * κq)) * (t ^ q - t ^ (q + 1))) (Ioc (0 : ℝ) 1) :=
      (hi1.sub hi2).const_mul _
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have : t ^ (q + 1) = t ^ q * t := Real.rpow_add_one ht.1.ne' q
    simp only [ha, this]; ring
  have hIa : ∫ t in Ioc (0 : ℝ) 1, a t = Λ * (n * R * κq) * (1 / ((q + 1) * (q + 2))) := by
    have : ∫ t in Ioc (0 : ℝ) 1, a t =
        ∫ t in Ioc (0 : ℝ) 1, (Λ * (n * R * κq)) * (t ^ q - t ^ (q + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      have : t ^ (q + 1) = t ^ q * t := Real.rpow_add_one ht.1.ne' q
      simp only [ha, this]; ring
    rw [this, integral_const_mul, integral_sub hi1 hi2, hI1, hI2]
    have h1 : q + 1 ≠ 0 := by linarith
    have h2 : q + 1 + 1 = q + 2 := by ring
    rw [h2]
    have h3 : q + 2 ≠ 0 := by linarith
    field_simp
    ring
  have hIb : ∫ t in Ioc (0 : ℝ) 1, b t = Λ * (Bc + B1 * κq / (q + 1)) := by
    simp only [hb]
    rw [integral_const_mul, integral_add hic ((hi1.const_mul κq).const_mul B1),
      integral_const_mul, integral_const_mul, hI1]
    rw [setIntegral_const]
    simp
    left
    ring
  have hla : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (a t) = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, a t) :=
    (ofReal_integral_eq_lintegral_ofReal hiat
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall ha0))).symm
  have hlb : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (b t) = ENNReal.ofReal (∫ t in Ioc (0 : ℝ) 1, b t) :=
    (ofReal_integral_eq_lintegral_ofReal hibt
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb0))).symm
  -- pointwise comparison
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) * Λ) * ENNReal.ofReal (v t) =
        ENNReal.ofReal ((1 - t) * Λ * v t) := fun t ht => by
    have h1 : 0 ≤ (1 - t) * Λ := mul_nonneg (by linarith [ht.2]) hΛ
    rw [ENNReal.ofReal_mul h1]
  have hdiff : ∀ t ∈ Ioc (0 : ℝ) 1, |(1 - t) * Λ * v t - a t| ≤ b t := fun t ht => by
    have h1 : 0 ≤ (1 - t) * Λ := mul_nonneg (by linarith [ht.2]) hΛ
    have h2 : (1 - t) * Λ * v t - a t = (1 - t) * Λ * (v t - n * R * (κq * t ^ q)) := by
      simp only [ha]; ring
    rw [h2, abs_mul, abs_of_nonneg h1]
    calc (1 - t) * Λ * |v t - n * R * (κq * t ^ q)| ≤ 1 * Λ * (Bc + B1 * (κq * t ^ q)) := by
          have := hv t ht
          have h3 : (1 - t) * Λ ≤ 1 * Λ := by nlinarith [ht.1]
          have h4 : 0 ≤ Bc + B1 * (κq * t ^ q) := by have := hq1 t ht; positivity
          calc (1 - t) * Λ * |v t - n * R * (κq * t ^ q)| ≤ (1 - t) * Λ * (Bc + B1 * (κq * t ^ q)) :=
                mul_le_mul_of_nonneg_left this h1
            _ ≤ 1 * Λ * (Bc + B1 * (κq * t ^ q)) := mul_le_mul_of_nonneg_right h3 h4
      _ = b t := by simp only [hb]; ring
  have hup : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((1 - t) * Λ) * ENNReal.ofReal (v t) ≤
        ENNReal.ofReal (a t) + ENNReal.ofReal (b t) := fun t ht => by
    rw [hpt t ht, ← ENNReal.ofReal_add (ha0 t ht) (hb0 t ht)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (abs_le.1 (hdiff t ht)).2
    linarith
  have hlow : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (a t) ≤
        ENNReal.ofReal ((1 - t) * Λ) * ENNReal.ofReal (v t) + ENNReal.ofReal (b t) := fun t ht => by
    have h1 : 0 ≤ (1 - t) * Λ := mul_nonneg (by linarith [ht.2]) hΛ
    rw [hpt t ht]
    calc ENNReal.ofReal (a t) ≤ ENNReal.ofReal ((1 - t) * Λ * v t + b t) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := (abs_le.1 (hdiff t ht)).1
          linarith
      _ ≤ _ := ENNReal.ofReal_add_le
  set A := Λ * (n * R * κq) * (1 / ((q + 1) * (q + 2))) with hA
  set B := Λ * (Bc + B1 * κq / (q + 1)) with hB
  have hA0 : 0 ≤ A := by
    have : 0 < q + 2 := by linarith
    have : 0 < q + 1 := by linarith
    simp only [hA]; positivity
  have hB0 : 0 ≤ B := by
    have : 0 < q + 1 := by linarith
    simp only [hB]; positivity
  have up : ENNReal.ofReal D ≤ ENNReal.ofReal (A + B) := by
    rw [hD, ENNReal.ofReal_add hA0 hB0, ← hIa, ← hIb, ← hla, ← hlb, ← lintegral_add_right _ hbm]
    exact setLIntegral_mono' measurableSet_Ioc hup
  have low : ENNReal.ofReal A ≤ ENNReal.ofReal (D + B) := by
    rw [ENNReal.ofReal_add hD0 hB0, hD, ← hIb, ← hlb, ← lintegral_add_right _ hbm, ← hIa, ← hla]
    exact setLIntegral_mono' measurableSet_Ioc hlow
  have u1 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 up
  have l1 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 low
  rw [abs_le]
  constructor <;> linarith

end Main

end HRS

end
