import HRS.Sections.AdjKGlueAux7

/-!
# ADJK-GLUE, part 8: tail bounds for `Ξ = Z + Rem` (Markov through rational times) and the Kolmogorov wrapper
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkg_rpow_half_sq (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem adjkg_two_half_le : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ 2 := by
  calc (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := ENNReal.rpow_one 2

/-- `√(2a + 2b) ≤ 2(√a + √b)`. -/
theorem adjkg_sqrt_add_le (a b : ℝ≥0∞) :
    (2 * a + 2 * b) ^ (1 / 2 : ℝ) ≤ 2 * (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) := by
  calc (2 * a + 2 * b) ^ (1 / 2 : ℝ) ≤ (2 * a) ^ (1 / 2 : ℝ) + (2 * b) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ = 2 ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) + 2 ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ ≤ 2 * a ^ (1 / 2 : ℝ) + 2 * b ^ (1 / 2 : ℝ) :=
        add_le_add (mul_le_mul_left adjkg_two_half_le _) (mul_le_mul_left adjkg_two_half_le _)
    _ = 2 * (a ^ (1 / 2 : ℝ) + b ^ (1 / 2 : ℝ)) := by rw [mul_add]

/-- Tail of the energy supremum of `Ξ = Z + Rem` (levels `j ≤ m₁`). -/
theorem adjkg_sup_tail {m m₁ j : ℝ} (hjm₁ : j ≤ m₁) {T : ℝ} (hT : 0 < T) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ξh Z : ℝ → Ω → NegSobolev d m)
    (hΞm : ∀ t, Measurable (Ξh t)) (hZm : ∀ t, Measurable (Z t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Ξh t ω) (Set.Icc 0 T)) {K₁ K₂ : ℝ} (hK₁0 : 0 ≤ K₁)
    (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy j m (Z t ω) ∂P ≤ ENNReal.ofReal K₁)
    (hK₂ : ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (adjkEnergy m₁ m (Ξh t ω - Z t ω)) ^ (1 / 2 : ℝ) ∂P ≤
      ENNReal.ofReal K₂) {R : ℝ} (hR : 0 < R) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m (Ξh t ω)} ≤
      ENNReal.ofReal (2 * (1 + K₁ + K₂) / R) := by
  set A : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ ratIcc 0 T, (adjkEnergy m₁ m (Z t ω)) ^ (1 / 2 : ℝ) with hA
  set B : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ ratIcc 0 T,
    (adjkEnergy m₁ m (Ξh t ω - Z t ω)) ^ (1 / 2 : ℝ) with hB
  have hAm : Measurable A := by
    refine Measurable.biSup _ (ratIcc_countable 0 T) fun t _ => ?_
    exact ((adjkEnergy_measurable m₁ m).comp (hZm t)).pow_const _
  have hBm : Measurable B := by
    refine Measurable.biSup _ (ratIcc_countable 0 T) fun t _ => ?_
    exact ((adjkEnergy_measurable m₁ m).comp ((hΞm t).sub (hZm t))).pow_const _
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m (Ξh t ω)} ≤ᵐ[P]
      {ω | ENNReal.ofReal (R / 2) ≤ A ω + B ω} := by
    filter_upwards [hcont] with ω hω hbad
    obtain ⟨t₀, ht₀, h₀⟩ := hbad
    obtain ⟨q, hq, hqlt⟩ := adjkg_rat_lsc hT (adjkEnergy m₁ m) (adjkEnergy_lsc m₁ m)
      (fun t => Ξh t ω) hω ht₀ h₀
    have hx : adjkEnergy m₁ m (Ξh q ω) ≤ 2 * adjkEnergy m₁ m (Ξh q ω - Z q ω) +
        2 * adjkEnergy m₁ m (Z q ω) := by
      have := adjkg_energy_add_le (m₁ := m₁) (Ξh q ω - Z q ω) (Z q ω)
      rwa [sub_add_cancel] at this
    have h1 : ENNReal.ofReal R < 2 * (A ω + B ω) := by
      have e1 : (ENNReal.ofReal (R ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal R := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hR.le]
      have h2 : (ENNReal.ofReal (R ^ 2)) ^ (1 / 2 : ℝ) < (adjkEnergy m₁ m (Ξh q ω)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_lt_rpow hqlt (by norm_num)
      rw [e1] at h2
      refine h2.trans_le ?_
      calc (adjkEnergy m₁ m (Ξh q ω)) ^ (1 / 2 : ℝ)
          ≤ (2 * adjkEnergy m₁ m (Ξh q ω - Z q ω) + 2 * adjkEnergy m₁ m (Z q ω)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hx (by norm_num)
        _ ≤ 2 * ((adjkEnergy m₁ m (Ξh q ω - Z q ω)) ^ (1 / 2 : ℝ) +
              (adjkEnergy m₁ m (Z q ω)) ^ (1 / 2 : ℝ)) := adjkg_sqrt_add_le _ _
        _ ≤ 2 * (B ω + A ω) := by
            refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
            · exact le_iSup₂_of_le q hq le_rfl
            · exact le_iSup₂_of_le q hq le_rfl
        _ = 2 * (A ω + B ω) := by rw [add_comm]
    have h3 : ENNReal.ofReal R = 2 * ENNReal.ofReal (R / 2) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    rw [h3] at h1
    exact (ENNReal.mul_lt_mul_iff_right (by norm_num) (by norm_num)).1 h1 |>.le
  have hAint : ∫⁻ ω, A ω ∂P ≤ ENNReal.ofReal (1 + K₁) := by
    have : ∀ ω, A ω ≤ 1 + ⨆ t ∈ ratIcc 0 T, adjkEnergy j m (Z t ω) := by
      intro ω
      refine iSup₂_le fun t ht => ?_
      refine (adjkg_sqrt_le _).trans ?_
      refine add_le_add le_rfl ?_
      exact (adjkEnergy_mono hjm₁ (Z t ω)).trans (le_iSup₂_of_le t ht le_rfl)
    have hgm : Measurable (fun ω => ⨆ t ∈ ratIcc 0 T, adjkEnergy j m (Z t ω)) := by
      refine Measurable.biSup _ (ratIcc_countable 0 T) fun t _ => ?_
      exact (adjkEnergy_measurable j m).comp (hZm t)
    calc ∫⁻ ω, A ω ∂P ≤ ∫⁻ ω, (1 + ⨆ t ∈ ratIcc 0 T, adjkEnergy j m (Z t ω)) ∂P := lintegral_mono this
      _ = 1 + ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, adjkEnergy j m (Z t ω) ∂P := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal K₁ := by
          rw [ENNReal.ofReal_one]
          exact add_le_add le_rfl hK₁
      _ = ENNReal.ofReal (1 + K₁) := (ENNReal.ofReal_add (by norm_num) hK₁0).symm
  have hint : ∫⁻ ω, (A ω + B ω) ∂P ≤ ENNReal.ofReal (1 + K₁ + K₂) := by
    rw [lintegral_add_left hAm]
    have hB' : ∫⁻ ω, B ω ∂P ≤ ENNReal.ofReal K₂ := hK₂
    calc ∫⁻ ω, A ω ∂P + ∫⁻ ω, B ω ∂P ≤ ENNReal.ofReal (1 + K₁) + ENNReal.ofReal K₂ :=
          add_le_add hAint hB'
      _ = ENNReal.ofReal (1 + K₁ + K₂) := (ENNReal.ofReal_add (by linarith) hK₂0).symm
  have hmk := adjkg_markov P (hAm.add hBm).aemeasurable hint (R := R / 2) (by positivity)
  calc P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (R ^ 2) < adjkEnergy m₁ m (Ξh t ω)}
      ≤ P {ω | ENNReal.ofReal (R / 2) ≤ A ω + B ω} := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal ((1 + K₁ + K₂) / (R / 2)) := hmk
    _ = ENNReal.ofReal (2 * (1 + K₁ + K₂) / R) := by
        congr 1
        field_simp

/-- Tail of the sup-norm of the remainder `Rm`, from its energy at a lower level. -/
theorem adjkg_rem_tail {m m₁ : ℝ} (hm₁ : m₁ ≤ m) {T : ℝ} (hT : 0 < T) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Rm : ℝ → Ω → NegSobolev d m)
    (hRm : ∀ t, Measurable (Rm t)) (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Rm t ω) (Set.Icc 0 T))
    {K : ℝ}
    (hK : ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (adjkEnergy m₁ m (Rm t ω)) ^ (1 / 2 : ℝ) ∂P ≤ ENNReal.ofReal K)
    {η : ℝ} (hη : 0 < η) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, η < ‖Rm t ω‖} ≤ ENNReal.ofReal (K / η) := by
  set B : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ ratIcc 0 T, (adjkEnergy m₁ m (Rm t ω)) ^ (1 / 2 : ℝ) with hB
  have hBm : Measurable B := by
    refine Measurable.biSup _ (ratIcc_countable 0 T) fun t _ => ?_
    exact ((adjkEnergy_measurable m₁ m).comp (hRm t)).pow_const _
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, η < ‖Rm t ω‖} ≤ᵐ[P] {ω | ENNReal.ofReal η ≤ B ω} := by
    filter_upwards [hcont] with ω hω hbad
    obtain ⟨t₀, ht₀, h₀⟩ := hbad
    have h₀' : ENNReal.ofReal η < ‖Rm t₀ ω‖ₑ := by
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff (hη.trans h₀)).2 h₀
    obtain ⟨q, hq, hqlt⟩ := adjkg_rat_lsc hT (fun F : NegSobolev d m => ‖F‖ₑ)
      continuous_enorm.lowerSemicontinuous (fun t => Rm t ω) hω ht₀ h₀'
    show ENNReal.ofReal η ≤ B ω
    refine hqlt.le.trans ?_
    refine le_iSup₂_of_le q hq ?_
    have := ENNReal.rpow_le_rpow (adjkg_enorm_sq_le_energy hm₁ (Rm q ω)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rwa [adjkg_rpow_half_sq] at this
  have hmk := adjkg_markov P hBm.aemeasurable hK hη
  exact (measure_mono_ae hsub).trans hmk

end HRS.AdjK
