import HRS.MD.EQBurnDefs

/-!
# EQ-BURN P4 (`eq_burnin_of_evo`), part 1: elementary lemmas

* `eqb_le_iSup_rat`: a function continuous on `[a,a+T]` (`T > 0`) is dominated there by its supremum over the rational times;
* `eqb_ratTimes_countable`;
* `eqb_exp_lintegral_le`: `∫_0^{a+T} (e^{-c(a-r)_+})² dr ≤ 1/(2c) + T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

open HRS.LZ

theorem eqb_ratTimes_countable (a T : ℝ) : (ratTimes a T).Countable := by
  refine (Set.countable_range (fun q : ℚ => (q : ℝ))).mono ?_
  rintro t ⟨-, q, rfl⟩
  exact ⟨q, rfl⟩

theorem eqb_mem_closure_ratTimes {a T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc a (a + T)) :
    t ∈ closure (ratTimes a T) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set lo : ℝ := max a (t - ε / 2) with hlo
  set hi : ℝ := min (a + T) (t + ε / 2) with hhi
  have hlh : lo < hi := by
    rw [hlo, hhi]
    refine max_lt (lt_min (by linarith) (by linarith [ht.1])) (lt_min (by linarith [ht.2]) (by linarith))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlh
  refine ⟨(q : ℝ), ⟨⟨?_, ?_⟩, q, rfl⟩, ?_⟩
  · exact (le_max_left _ _).trans hq1.le
  · exact hq2.le.trans (min_le_left _ _)
  · have h1 : t - ε / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have h2 : (q : ℝ) < t + ε / 2 := lt_of_lt_of_le hq2 (min_le_right _ _)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith

/-- A function continuous on `[a,a+T]` is dominated by its supremum over the rational times. -/
theorem eqb_le_iSup_rat {a T : ℝ} (hT : 0 < T) (f : ℝ → ℝ≥0∞) (hf : ContinuousOn f (Set.Icc a (a + T)))
    {t : ℝ} (ht : t ∈ Set.Icc a (a + T)) : f t ≤ ⨆ q ∈ ratTimes a T, f q := by
  have hcl := eqb_mem_closure_ratTimes hT ht
  have : (𝓝[ratTimes a T] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hsub : ratTimes a T ⊆ Set.Icc a (a + T) := fun q hq => hq.1
  have hcw : ContinuousWithinAt f (ratTimes a T) t := (hf t ht).mono hsub
  refine le_of_tendsto hcw.tendsto ?_
  exact eventually_nhdsWithin_of_forall fun q hq => le_iSup₂ (f := fun q (_ : q ∈ ratTimes a T) => f q) q hq

theorem eqb_exp_lintegral_le {c : ℝ} (hc : 0 < c) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) ≤
      ENNReal.ofReal (1 / (2 * c) + T) := by
  have hsplit : Set.Icc (0 : ℝ) (a + T) ⊆ Set.Icc 0 a ∪ Set.Ioc a (a + T) := by
    intro r hr
    by_cases h : r ≤ a
    · exact Or.inl ⟨hr.1, h⟩
    · exact Or.inr ⟨not_le.1 h, hr.2⟩
  have h1 : ∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) ≤
      ENNReal.ofReal (1 / (2 * c)) := by
    have hint : ∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) =
        ∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (Real.exp (-(2 * c) * (a - r))) := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      rw [max_eq_left (by linarith [hr.2]), ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    rw [hint, ← ofReal_integral_eq_lintegral_ofReal]
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
      rw [intervalIntegral.integral_comp_sub_left (fun x => Real.exp (-(2 * c) * x)) a]
      simp only [sub_self, sub_zero]
      rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by linarith : -(2 * c) ≠ 0)]
      simp only [integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
      have h2 : 0 ≤ Real.exp (-(2 * c) * a) := (Real.exp_pos _).le
      have : (-(2 * c))⁻¹ * (Real.exp (-(2 * c) * a) - 1) = (1 - Real.exp (-(2 * c) * a)) / (2 * c) := by
        field_simp
        ring
      rw [this]
      rw [div_le_div_iff_of_pos_right (by linarith)]
      linarith
    · exact (continuous_const.mul (continuous_const.sub continuous_id)).rexp.integrableOn_Icc
    · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have h2 : ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) ≤
      ENNReal.ofReal T := by
    have : ∀ r ∈ Set.Ioc a (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) ≤ 1 := by
      intro r hr
      rw [max_eq_right (by linarith [hr.1])]
      simp
    calc ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2)
        ≤ ∫⁻ r in Set.Ioc a (a + T), 1 := setLIntegral_mono measurable_const this
      _ = ENNReal.ofReal T := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
          one_mul]
        congr 1; ring
  calc ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2)
      ≤ ∫⁻ r in Set.Icc 0 a ∪ Set.Ioc a (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) :=
        lintegral_mono_set hsplit
    _ ≤ (∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2)) +
          ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (1 / (2 * c)) + ENNReal.ofReal T := add_le_add h1 h2
    _ = ENNReal.ofReal (1 / (2 * c) + T) := by
        rw [ENNReal.ofReal_add (by positivity) hT]

end HRS.MD.EQBurnBurn

end
