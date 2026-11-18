import HRS.MD.EQRemInt10

/-!
# EQ-REM (b), part 11: the weight `∫_0^{a+T} K' e^{-c (a-r)_+} dr ≤ K' (1/c + T)`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

theorem eqrem_weight_bound {K' c a T : ℝ} (hK' : 0 ≤ K') (hc : 0 < c) (ha : 0 ≤ a) (hT : 0 ≤ T) :
    ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) ≤
      ENNReal.ofReal (K' * (1 / c + T)) := by
  have hsub : Set.Ioc 0 (a + T) ⊆ Set.Ioc 0 a ∪ Set.Ioc a (a + T) := by
    intro r hr
    by_cases h : r ≤ a
    · exact Or.inl ⟨hr.1, h⟩
    · exact Or.inr ⟨not_le.1 h, hr.2⟩
  have h1 : ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) ≤
      ENNReal.ofReal (K' * (1 / c)) := by
    have e1 : ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) =
        ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (K' * Real.exp (-c * (a - r))) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
      rw [max_eq_left (by linarith [hr.2])]
    have hcont : Continuous fun r : ℝ => K' * Real.exp (-c * (a - r)) := by fun_prop
    have e2 : ∫⁻ r in Set.Ioc 0 a, ENNReal.ofReal (K' * Real.exp (-c * (a - r))) =
        ENNReal.ofReal (∫ r in Set.Ioc 0 a, K' * Real.exp (-c * (a - r))) :=
      (ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Ioc)
        (ae_of_all _ fun r => mul_nonneg hK' (Real.exp_pos _).le)).symm
    rw [e1, e2]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← intervalIntegral.integral_of_le ha, intervalIntegral.integral_const_mul]
    have hd : ∀ r ∈ Set.uIcc (0 : ℝ) a, HasDerivAt (fun r => Real.exp (-c * (a - r)) / c)
        (Real.exp (-c * (a - r))) r := by
      intro r _
      have h1 : HasDerivAt (fun r : ℝ => -c * (a - r)) c r := by
        have := ((hasDerivAt_id r).const_sub a).const_mul (-c)
        simpa using this
      have := h1.exp.div_const c
      convert this using 1
      field_simp
    have hint : IntervalIntegrable (fun r : ℝ => Real.exp (-c * (a - r))) volume 0 a := by
      exact (by fun_prop : Continuous fun r : ℝ => Real.exp (-c * (a - r))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    have : Real.exp (-c * (a - a)) / c - Real.exp (-c * (a - 0)) / c ≤ 1 / c := by
      simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
      have : 0 ≤ Real.exp (-c * a) / c := div_nonneg (Real.exp_pos _).le hc.le
      linarith
    exact mul_le_mul_of_nonneg_left this hK'
  have h2 : ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) =
      ENNReal.ofReal K' * ENNReal.ofReal T := by
    have e1 : ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) =
        ∫⁻ r in Set.Ioc a (a + T), ENNReal.ofReal K' := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
      rw [max_eq_right (by linarith [hr.1])]; simp
    rw [e1, setLIntegral_const, Real.volume_Ioc]
    congr 2; ring
  calc ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0))
      ≤ ∫⁻ r in Set.Ioc 0 a ∪ Set.Ioc a (a + T),
          ENNReal.ofReal (K' * Real.exp (-c * max (a - r) 0)) := lintegral_mono_set hsub
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (K' * (1 / c)) + ENNReal.ofReal K' * ENNReal.ofReal T := by
        rw [h2]; exact add_le_add h1 le_rfl
    _ = ENNReal.ofReal (K' * (1 / c + T)) := by
        rw [← ENNReal.ofReal_mul hK', ← ENNReal.ofReal_add (mul_nonneg hK' (by positivity))
          (mul_nonneg hK' hT)]
        congr 1; ring

end HRS.MD.EQRem

end
