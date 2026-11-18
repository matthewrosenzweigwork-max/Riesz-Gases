import HRS.MS.R2ChaosAux49

/-!
# HRS.MS.R2ChaosAux50 -- (e) part 5: `W_r → 0` in a Hilbert space from weak convergence and uniform moments

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_wass_H`: if `μ_N → μ` weakly on a separable Hilbert space `H` and `sup_N ∫ ‖x‖^q dμ_N < ∞` for every `q ≥ 2`, then
`W_r(μ_N, μ) → 0` for every `r ≥ 1` (`W_2` from `wassersteinE_two_tendsto_of_weak`, monotonicity for `r ≤ 2`, `s94_wass_interp` for `r > 2`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

section WassH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s94_integrable_sq_of_fourth (ν : Measure H) [IsProbabilityMeasure ν] {M : ℝ}
    (hM : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (4 : ℝ)) ∂ν ≤ ENNReal.ofReal M) :
    Integrable (fun x : H => ‖x‖ ^ 2) ν := by
  have hm : Measurable fun x : H => ‖x‖ ^ 2 := continuous_norm.measurable.pow_const 2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have h1 : ∀ x : H, ‖‖x‖ ^ 2‖ₑ ≤ 1 + ENNReal.ofReal (‖x‖ ^ (4 : ℝ)) := by
    intro x
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ (4 : ℝ) := by
      have h4 : ‖x‖ ^ (4 : ℝ) = (‖x‖ ^ 2) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num
      rw [h4]; nlinarith [sq_nonneg (‖x‖ ^ 2 - 1)]
    calc ENNReal.ofReal (‖x‖ ^ 2) ≤ ENNReal.ofReal (1 + ‖x‖ ^ (4 : ℝ)) := ENNReal.ofReal_le_ofReal this
      _ = 1 + ENNReal.ofReal (‖x‖ ^ (4 : ℝ)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity)]; simp
  refine lt_of_le_of_lt (lintegral_mono h1) ?_
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_lt hM ENNReal.ofReal_lt_top⟩

theorem s94_lintegral_sq_eq_ofReal (ν : Measure H) (hI : Integrable (fun x : H => ‖x‖ ^ 2) ν) :
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, ‖x‖ ^ 2 ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

theorem s94_sq_rpow_two (x : H) : (‖x‖ ^ 2) ^ (2 : ℝ) = ‖x‖ ^ (4 : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]; norm_num

theorem s94_wass_H (μN : ℕ → ProbabilityMeasure H) (μ : ProbabilityMeasure H) (hweak : Tendsto μN atTop (𝓝 μ))
    (hmom : ∀ q : ℝ, 2 ≤ q → ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N in atTop,
      ∫⁻ x, ENNReal.ofReal (‖x‖ ^ q) ∂(μN N : Measure H) ≤ ENNReal.ofReal M)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun N => HRS.wassersteinE r (μN N : Measure H) (μ : Measure H)) atTop (𝓝 0) := by
  obtain ⟨M4, hM40, hM4⟩ := hmom 4 (by norm_num)
  have h4 : ∀ᶠ N in atTop, ∫⁻ x, ENNReal.ofReal ((‖x‖ ^ 2) ^ (2 : ℝ)) ∂(μN N : Measure H) ≤ ENNReal.ofReal M4 := by
    filter_upwards [hM4] with N hN
    refine le_trans (le_of_eq ?_) hN
    exact lintegral_congr fun x => by rw [s94_sq_rpow_two]
  obtain ⟨hint, hlim, hlimM⟩ := s94_weak_integral_tendsto hweak (g := fun x : H => ‖x‖ ^ 2)
    (continuous_norm.pow 2) (fun x => by positivity) (q := 2) (by norm_num) hM40 h4
  have hμ4 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (4 : ℝ)) ∂(μ : Measure H) ≤ ENNReal.ofReal M4 := by
    refine le_trans (le_of_eq ?_) hlimM
    exact lintegral_congr fun x => by rw [s94_sq_rpow_two]
  have hfin : ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H) < ⊤ := by
    rw [s94_lintegral_sq_eq_ofReal _ hint]; exact ENNReal.ofReal_lt_top
  have hmom2 : Tendsto (fun N => ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μN N : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H))) := by
    rw [s94_lintegral_sq_eq_ofReal _ hint]
    have h1 := ENNReal.tendsto_ofReal hlim
    refine (tendsto_congr' ?_).2 h1
    filter_upwards [hM4] with N hN
    exact (s94_lintegral_sq_eq_ofReal _ (s94_integrable_sq_of_fourth _ hN))
  have hW2 : Tendsto (fun N => HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H)) atTop (𝓝 0) :=
    HRS.wassersteinE_two_tendsto_of_weak μN μ hweak hfin hmom2
  rcases le_total r 2 with hr2 | hr2
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hW2 (fun N => bot_le) (fun N => ?_)
    exact HRS.wassersteinE_mono r 2 hr hr2 _ _
  · -- interpolation
    obtain ⟨M, hM0, hMN⟩ := hmom (2 * r - 2) (by linarith)
    have hMμ : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂(μ : Measure H) ≤ ENNReal.ofReal M :=
      s94_lintegral_le_of_weak hweak (continuous_norm.rpow_const fun _ => Or.inr (by linarith))
        (fun x => Real.rpow_nonneg (norm_nonneg _) _) hM0 hMN
    set K : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (2 ^ (2 * r - 1) * M)) with hK
    have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
    have hεN : Tendsto (fun N : ℕ => ENNReal.ofReal (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    have hsum : Tendsto (fun N => (HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H) +
        ENNReal.ofReal (1 / ((N : ℝ) + 1))) * K) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N => HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H) +
          ENNReal.ofReal (1 / ((N : ℝ) + 1))) atTop (𝓝 (0 + 0)) := hW2.add hεN
      have h2 : Tendsto (fun N => (HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H) +
          ENNReal.ofReal (1 / ((N : ℝ) + 1))) * K) atTop (𝓝 ((0 + 0) * K)) :=
        ENNReal.Tendsto.mul_const h1 (Or.inr hKt)
      simpa using h2
    have hrp : Tendsto (fun N => ((HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H) +
        ENNReal.ofReal (1 / ((N : ℝ) + 1))) * K) ^ (1 / r)) atTop (𝓝 0) := by
      have hr0 : 0 < 1 / r := by positivity
      have h3 : Tendsto (fun N => ((HRS.wassersteinE 2 (μN N : Measure H) (μ : Measure H) +
          ENNReal.ofReal (1 / ((N : ℝ) + 1))) * K) ^ (1 / r)) atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / r))) :=
        ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp hsum
      rwa [ENNReal.zero_rpow_of_pos hr0] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrp (Eventually.of_forall fun N => bot_le) ?_
    have hW2fin := hW2.eventually (gt_mem_nhds (ENNReal.zero_lt_top))
    filter_upwards [hW2fin, hMN] with N hN hMN'
    exact s94_wass_interp (μN N : Measure H) (μ : Measure H) hr2 hM0 hMN' hMμ hN.ne
      (ENNReal.ofReal_pos.2 (by positivity)).ne'

end WassH

end HRS.MS.R2Chaos
