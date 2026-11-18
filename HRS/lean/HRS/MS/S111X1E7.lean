import HRS.MS.S111X1E6

/-!
# S11.1 X1 (energy), part 7: the Gronwall step
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

theorem hasDerivAt_primitive {g : ℝ → ℝ} {t : ℝ} (hg : ContinuousOn g (Set.Icc 0 t)) {r : ℝ}
    (hr : r ∈ Set.Ioo 0 t) : HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, g v) (g r) r := by
  have hint : IntervalIntegrable g volume 0 r :=
    (hg.mono (Set.uIcc_subset_Icc ⟨le_rfl, hr.1.le.trans hr.2.le⟩ ⟨hr.1.le, hr.2.le⟩)).intervalIntegrable
  have hca : ContinuousAt g r := hg.continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hsm : StronglyMeasurableAtFilter g (𝓝 r) :=
    (hg.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
  exact intervalIntegral.integral_hasDerivAt_right hint hsm hca

theorem gronwall_gen {t : ℝ} (ht : 0 ≤ t) {Φ Dd : ℝ → ℝ} {C₂ β : ℝ} (hβ : 0 < β) (hC₂ : 0 ≤ C₂)
    (hΦc : ContinuousOn Φ (Set.Icc 0 t)) (hDc : ContinuousOn Dd (Set.Icc 0 t))
    (hder : ∀ r ∈ Set.Ioo 0 t, ∃ Φ' : ℝ, HasDerivAt Φ Φ' r ∧ β⁻¹ * Dd r - C₂ * Φ r ≤ Φ')
    (hD0 : ∀ r ∈ Set.Icc 0 t, 0 ≤ Dd r) (hΦ0 : ∀ r ∈ Set.Icc 0 t, 0 ≤ Φ r) :
    (∀ r ∈ Set.Icc 0 t, Φ r ≤ Real.exp (C₂ * (t - r)) * Φ t) ∧
      ∫ r in Set.Icc 0 t, Dd r ≤ β * (Φ t + C₂ * t * Real.exp (C₂ * t) * Φ t) := by
  have hβi : 0 < β⁻¹ := inv_pos.2 hβ
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  -- part A
  have hA : ∀ r ∈ Set.Icc 0 t, Φ r ≤ Real.exp (C₂ * (t - r)) * Φ t := by
    have hmono : MonotoneOn (fun r => Real.exp (C₂ * r) * Φ r) (Set.Icc 0 t) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hΦc)
        (fun r hr => ?_) (fun r hr => ?_)
      · rw [interior_Icc] at hr
        obtain ⟨Φ', hΦ', -⟩ := hder r hr
        have h1 : HasDerivAt (fun r => Real.exp (C₂ * r)) (Real.exp (C₂ * r) * C₂) r := by
          have := ((hasDerivAt_id r).const_mul C₂).exp
          simpa using this
        exact (h1.mul hΦ').differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hr
        obtain ⟨Φ', hΦ', hineq⟩ := hder r hr
        have h1 : HasDerivAt (fun r => Real.exp (C₂ * r)) (Real.exp (C₂ * r) * C₂) r := by
          have := ((hasDerivAt_id r).const_mul C₂).exp
          simpa using this
        have hd : HasDerivAt (fun r => Real.exp (C₂ * r) * Φ r)
            (Real.exp (C₂ * r) * C₂ * Φ r + Real.exp (C₂ * r) * Φ') r := h1.mul hΦ'
        rw [hd.deriv]
        have := hD0 r (Set.Ioo_subset_Icc_self hr)
        have h3 : 0 ≤ β⁻¹ * Dd r := mul_nonneg hβi.le this
        have := Real.exp_pos (C₂ * r)
        nlinarith
    intro r hr
    have := hmono hr ht' hr.2
    simp only at this
    have e : Real.exp (C₂ * (t - r)) = Real.exp (C₂ * t) * Real.exp (-(C₂ * r)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h2 : Real.exp (C₂ * r) * Real.exp (-(C₂ * r)) = 1 := by rw [← Real.exp_add]; simp
    calc Φ r = Real.exp (-(C₂ * r)) * (Real.exp (C₂ * r) * Φ r) := by
          rw [← mul_assoc, mul_comm (Real.exp (-(C₂ * r))), h2, one_mul]
      _ ≤ Real.exp (-(C₂ * r)) * (Real.exp (C₂ * t) * Φ t) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = Real.exp (C₂ * t) * Real.exp (-(C₂ * r)) * Φ t := by ring
  refine ⟨hA, ?_⟩
  -- part B
  have hIΦ : IntervalIntegrable Φ volume 0 t := hΦc.intervalIntegrable_of_Icc ht
  have hID : IntervalIntegrable Dd volume 0 t := hDc.intervalIntegrable_of_Icc ht
  have hmonoB : MonotoneOn (fun r => Φ r + C₂ * (∫ v in (0 : ℝ)..r, Φ v) - β⁻¹ * ∫ v in (0 : ℝ)..r, Dd v)
      (Set.Icc 0 t) := by
    have cI : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc 0 t) →
        ContinuousOn (fun r => ∫ v in (0 : ℝ)..r, g v) (Set.Icc 0 t) := by
      intro g hg
      have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t) (μ := volume)
        (hg.integrableOn_Icc.mono_set (by rw [Set.uIcc_of_le ht]))
      rwa [Set.uIcc_of_le ht] at this
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((hΦc.add ((cI Φ hΦc).const_smul C₂)).sub ((cI Dd hDc).const_smul β⁻¹)) (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Icc] at hr
      obtain ⟨Φ', hΦ', -⟩ := hder r hr
      have h1 := hasDerivAt_primitive hΦc hr
      have h2 := hasDerivAt_primitive hDc hr
      exact ((hΦ'.add (h1.const_mul C₂)).sub (h2.const_mul β⁻¹)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hr
      obtain ⟨Φ', hΦ', hineq⟩ := hder r hr
      have h1 := hasDerivAt_primitive hΦc hr
      have h2 := hasDerivAt_primitive hDc hr
      have hd : HasDerivAt (fun r => Φ r + C₂ * (∫ v in (0 : ℝ)..r, Φ v) - β⁻¹ * ∫ v in (0 : ℝ)..r, Dd v)
          (Φ' + C₂ * Φ r - β⁻¹ * Dd r) r := (hΦ'.add (h1.const_mul C₂)).sub (h2.const_mul β⁻¹)
      rw [hd.deriv]
      linarith
  have hB := hmonoB h0' ht' ht
  simp only [intervalIntegral.integral_same, mul_zero, add_zero, sub_zero] at hB
  have hbound : ∫ v in (0 : ℝ)..t, Φ v ≤ ∫ v in (0 : ℝ)..t, Real.exp (C₂ * t) * Φ t := by
    refine intervalIntegral.integral_mono_on ht hIΦ intervalIntegrable_const (fun v hv => ?_)
    refine (hA v ⟨hv.1, hv.2⟩).trans ?_
    have : Real.exp (C₂ * (t - v)) ≤ Real.exp (C₂ * t) :=
      Real.exp_le_exp.2 (by nlinarith [hv.1])
    exact mul_le_mul_of_nonneg_right this (hΦ0 t ht')
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hbound
  have hset : ∫ r in Set.Icc 0 t, Dd r = ∫ v in (0 : ℝ)..t, Dd v := by
    rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
  rw [hset]
  have hΦ00 := hΦ0 0 h0'
  have : β⁻¹ * ∫ v in (0 : ℝ)..t, Dd v ≤ Φ t + C₂ * (t * (Real.exp (C₂ * t) * Φ t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hbound hC₂]
  calc ∫ v in (0 : ℝ)..t, Dd v = β * (β⁻¹ * ∫ v in (0 : ℝ)..t, Dd v) := by
        rw [← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
    _ ≤ β * (Φ t + C₂ * (t * (Real.exp (C₂ * t) * Φ t))) := mul_le_mul_of_nonneg_left this hβ.le
    _ = β * (Φ t + C₂ * t * Real.exp (C₂ * t) * Φ t) := by ring

end HRS.MS.S111X1
