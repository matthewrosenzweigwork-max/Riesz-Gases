import HRS.MS.S82RN2

/-!
# S8.2 R02 (S82R), N3: the critical double convolution is logarithmic
`int q(z-u) q(u-p) dmu(u) <= C (1 + log(1 + q(z-p)))`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem s82r_conv2 (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ z p : Euc d, z ≠ p →
        Integrable (fun u => q (z - u) * q (u - p)) (HRS.Whole.withDensityReal ρ) ∧
        ∫ u, q (z - u) * q (u - p) ∂(HRS.Whole.withDensityReal ρ) ≤
          C * (1 + Real.log (1 + q (z - p))) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := s82r_rows hd hq M
  obtain ⟨L₁, C₂, hL₁, hC₂, hdisj⟩ := s82r_disjoint hd1 hq
  refine ⟨Cb * (1 + Real.log L₁ + Real.log (1 + C₂)) + 2 * Ca + Cb, by
    have := Real.log_nonneg hL₁
    have h2 : 0 ≤ Real.log (1 + C₂) := Real.log_nonneg (by linarith)
    positivity, fun ρ hρ hM z p hzp => ?_⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hq0 := hq.nonneg
  set L : ℝ := L₁ + C₂ * q (z - p) with hLdef
  have hq1 : 0 ≤ q (z - p) := hq0 _
  have hLge : L₁ ≤ L := by rw [hLdef]; nlinarith
  have hL1 : 1 ≤ L := hL₁.trans hLge
  have hLpos : 0 < L := by linarith
  have hCL : C₂ * q (z - p) < L := by rw [hLdef]; linarith
  -- rows
  obtain ⟨hz1, hz2⟩ := H ρ hρ hM z
  obtain ⟨hp1, hp2⟩ := H ρ hρ hM p
  obtain ⟨hai, haI⟩ := hz1 L hLpos
  obtain ⟨hbi, hbI⟩ := hp1 L hLpos
  obtain ⟨hal, halI⟩ := hz2 L hL1
  obtain ⟨hbl, hblI⟩ := hp2 L hL1
  have hev : ∀ u, q (u - p) = q (p - u) := fun u => by
    rw [← hq.even (p - u), neg_sub]
  -- a.e. pointwise bound
  have hae : ∀ᵐ u ∂μ, u ≠ z ∧ u ≠ p := by
    have h1 := HRS.MS.S82P2.s82p2_mu_singleton hd ρ z
    have h2 := HRS.MS.S82P2.s82p2_mu_singleton hd ρ p
    rw [ae_iff]
    have : {u | ¬(u ≠ z ∧ u ≠ p)} ⊆ {z} ∪ {p} := fun u hu => by
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hu
      rcases hu with h | h <;> simp [h]
    exact measure_mono_null this (measure_union_null h1 h2)
  have hg : Integrable (fun u => (min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2 +
      L * max (q (z - u) - L) 0 + L * max (q (p - u) - L) 0) μ :=
    (((hal.div_const 2).add (hbl.div_const 2)).add (hai.const_mul L)).add (hbi.const_mul L)
  have hmeasf : Measurable (fun u => q (z - u) * q (u - p)) :=
    (hq.measurable.comp (measurable_const.sub measurable_id)).mul
      (hq.measurable.comp (measurable_id.sub measurable_const))
  have hbd : ∀ᵐ u ∂μ, q (z - u) * q (u - p) ≤ (min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2 +
      L * max (q (z - u) - L) 0 + L * max (q (p - u) - L) 0 := by
    filter_upwards [hae] with u ⟨huz, hup⟩
    rw [hev u]
    have hdj := hdisj z p u L hzp huz hup hLge hCL
    set a := q (z - u) with ha
    set b := q (p - u) with hb
    have ha0 : 0 ≤ a := hq0 _
    have hb0 : 0 ≤ b := hq0 _
    have hnot : ¬ (L < a ∧ L < b) := hdj
    have e1 : a = min a L + max (a - L) 0 := by
      rcases le_total a L with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have e2 : b = min b L + max (b - L) 0 := by
      rcases le_total b L with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have haL : min a L ≤ L := min_le_right _ _
    have hbL : min b L ≤ L := min_le_right _ _
    have haL0 : 0 ≤ min a L := le_min ha0 hLpos.le
    have hbL0 : 0 ≤ min b L := le_min hb0 hLpos.le
    have haH0 : 0 ≤ max (a - L) 0 := le_max_right _ _
    have hbH0 : 0 ≤ max (b - L) 0 := le_max_right _ _
    have hprod : max (a - L) 0 * max (b - L) 0 = 0 := by
      by_contra h
      have h1 : max (a - L) 0 ≠ 0 := fun h' => h (by rw [h', zero_mul])
      have h2 : max (b - L) 0 ≠ 0 := fun h' => h (by rw [h', mul_zero])
      apply hnot
      constructor
      · by_contra hh; push Not at hh; exact h1 (max_eq_right (by linarith))
      · by_contra hh; push Not at hh; exact h2 (max_eq_right (by linarith))
    have hsq : min a L * min b L ≤ (min a L) ^ 2 / 2 + (min b L) ^ 2 / 2 := by
      nlinarith [sq_nonneg (min a L - min b L)]
    calc a * b = (min a L + max (a - L) 0) * (min b L + max (b - L) 0) := by rw [← e1, ← e2]
      _ = min a L * min b L + min a L * max (b - L) 0 + max (a - L) 0 * min b L +
            max (a - L) 0 * max (b - L) 0 := by ring
      _ ≤ (min a L) ^ 2 / 2 + (min b L) ^ 2 / 2 + L * max (b - L) 0 + L * max (a - L) 0 + 0 := by
          rw [hprod]
          have h3 : min a L * max (b - L) 0 ≤ L * max (b - L) 0 := mul_le_mul_of_nonneg_right haL hbH0
          have h4 : max (a - L) 0 * min b L ≤ max (a - L) 0 * L := mul_le_mul_of_nonneg_left hbL haH0
          nlinarith [hsq, h3, h4]
      _ = _ := by ring
  have hint : Integrable (fun u => q (z - u) * q (u - p)) μ :=
    Integrable.mono' hg hmeasf.aestronglyMeasurable (by
      filter_upwards [hbd] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hq0 _))]; exact hu)
  have hle : ∫ u, q (z - u) * q (u - p) ∂μ ≤ ∫ u, ((min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2 +
      L * max (q (z - u) - L) 0 + L * max (q (p - u) - L) 0) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (hq0 _) (hq0 _)) hg hbd
  refine ⟨hint, hle.trans ?_⟩
  have hI : ∫ u, ((min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2 +
      L * max (q (z - u) - L) 0 + L * max (q (p - u) - L) 0) ∂μ =
      (∫ u, (min (q (z - u)) L) ^ 2 ∂μ) / 2 + (∫ u, (min (q (p - u)) L) ^ 2 ∂μ) / 2 +
        L * ∫ u, max (q (z - u) - L) 0 ∂μ + L * ∫ u, max (q (p - u) - L) 0 ∂μ := by
    have i1 : Integrable (fun u => (min (q (z - u)) L) ^ 2 / 2) μ := hal.div_const 2
    have i2 : Integrable (fun u => (min (q (p - u)) L) ^ 2 / 2) μ := hbl.div_const 2
    have i3 : Integrable (fun u => L * max (q (z - u) - L) 0) μ := hai.const_mul L
    have i4 : Integrable (fun u => L * max (q (p - u) - L) 0) μ := hbi.const_mul L
    have i12 : Integrable (fun u => (min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2) μ :=
      i1.add i2
    have i123 : Integrable (fun u => (min (q (z - u)) L) ^ 2 / 2 + (min (q (p - u)) L) ^ 2 / 2 +
        L * max (q (z - u) - L) 0) μ := i12.add i3
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_div, integral_div,
      integral_const_mul, integral_const_mul]
  rw [hI]
  have h1 : L * ∫ u, max (q (z - u) - L) 0 ∂μ ≤ Ca := by
    calc L * ∫ u, max (q (z - u) - L) 0 ∂μ ≤ L * (Ca / L) := mul_le_mul_of_nonneg_left haI hLpos.le
      _ = Ca := by field_simp
  have h2 : L * ∫ u, max (q (p - u) - L) 0 ∂μ ≤ Ca := by
    calc L * ∫ u, max (q (p - u) - L) 0 ∂μ ≤ L * (Ca / L) := mul_le_mul_of_nonneg_left hbI hLpos.le
      _ = Ca := by field_simp
  have hlogL : Real.log (Real.exp 1 * L) ≤ 1 + Real.log L₁ + Real.log (1 + C₂) + Real.log (1 + q (z - p)) := by
    rw [Real.log_mul (Real.exp_pos _).ne' hLpos.ne', Real.log_exp]
    have hL' : L ≤ L₁ * ((1 + C₂) * (1 + q (z - p))) := by
      rw [hLdef]; nlinarith [mul_nonneg hC₂ hq1, mul_nonneg (mul_nonneg hC₂ hq1) (by linarith : (0:ℝ) ≤ L₁ - 1),
        mul_nonneg (by linarith : (0:ℝ) ≤ L₁ - 1) hq1, mul_nonneg (by linarith : (0:ℝ) ≤ L₁ - 1) hC₂]
    have := Real.log_le_log hLpos hL'
    rw [Real.log_mul (by linarith) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
    linarith
  have hCb' : (∫ u, (min (q (z - u)) L) ^ 2 ∂μ) / 2 + (∫ u, (min (q (p - u)) L) ^ 2 ∂μ) / 2 ≤
      Cb * Real.log (Real.exp 1 * L) := by linarith
  have hlogq : 0 ≤ Real.log (1 + q (z - p)) := Real.log_nonneg (by linarith)
  have hl1 : 0 ≤ Real.log L₁ := Real.log_nonneg hL₁
  have hl2 : 0 ≤ Real.log (1 + C₂) := Real.log_nonneg (by linarith)
  calc _ ≤ Cb * Real.log (Real.exp 1 * L) + Ca + Ca := by linarith
    _ ≤ Cb * (1 + Real.log L₁ + Real.log (1 + C₂) + Real.log (1 + q (z - p))) + Ca + Ca := by
        have := mul_le_mul_of_nonneg_left hlogL hCb; linarith
    _ ≤ _ := by nlinarith [mul_nonneg hCb hlogq, mul_nonneg hCb hl1, mul_nonneg hCb hl2, hCa]

end HRS.MS.S82R

end
