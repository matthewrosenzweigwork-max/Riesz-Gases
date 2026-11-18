import HRS.Prob.Metrics

/-!
# S2.1 packet 31c: approximate couplings from upper bounds on `wassersteinE`

Generic facts: an upper bound (strict, against any `c`) on the infimum defining
`HRS.wassersteinE` yields an actual coupling whose cost is below `c`.  The
infimum need not be attained, so this uses the strict inequality `< c` and
`iInf_lt_iff`, not an attaining coupling.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- If `W_p(P,Q) < c`, some coupling `π` of `P` and `Q` has cost `(∫ ‖x-y‖^p dπ)^{1/p} < c`. -/
theorem fp81s21_exists_coupling_of_wassersteinE_lt {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] (p : ℝ) (P Q : Measure B)
    {c : ℝ≥0∞} (h : HRS.wassersteinE p P Q < c) :
    ∃ π : Measure (B × B), HRS.IsCoupling π P Q ∧
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π) ^ (1 / p) < c := by
  unfold HRS.wassersteinE at h
  rw [iInf_lt_iff] at h
  obtain ⟨⟨π, hπ⟩, hlt⟩ := h
  exact ⟨π, hπ, hlt⟩

/-- A coupling of a probability measure `P` with any `Q` is a probability measure. -/
theorem fp81s21_isProbabilityMeasure_of_isCoupling {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] {P Q : Measure B}
    [IsProbabilityMeasure P] {π : Measure (B × B)} (hπ : HRS.IsCoupling π P Q) :
    IsProbabilityMeasure π :=
  HRS.IsCoupling.isProbabilityMeasure hπ

/-- Approximate `W_1`-coupling: if `W_1(P,Q) ≤ d` then for every `η > 0` there is a
probability coupling `π` of `P` and `Q` with integrable cost and `∫ ‖x-y‖ dπ ≤ d + η`.
Second countability of `B` is needed for measurability of `(x,y) ↦ ‖x-y‖` on `B × B`. -/
theorem fp81s21_exists_coupling_of_W1_le {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℝ} (hd : 0 ≤ d) (hW : HRS.wassersteinE 1 P Q ≤ ENNReal.ofReal d)
    {η : ℝ} (hη : 0 < η) :
    ∃ π : Measure (B × B), IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧
      Integrable (fun z : B × B => ‖z.1 - z.2‖) π ∧ ∫ z, ‖z.1 - z.2‖ ∂π ≤ d + η := by
  have hlt : HRS.wassersteinE 1 P Q < ENNReal.ofReal (d + η) :=
    lt_of_le_of_lt hW ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨π, hπc, hcost⟩ := fp81s21_exists_coupling_of_wassersteinE_lt 1 P Q hlt
  have hprob : IsProbabilityMeasure π := HRS.IsCoupling.isProbabilityMeasure hπc
  have hcost1 : ∫⁻ z : B × B, ENNReal.ofReal ‖z.1 - z.2‖ ∂π < ENNReal.ofReal (d + η) := by
    have e1 : (1 : ℝ) / 1 = 1 := by norm_num
    rw [e1, ENNReal.rpow_one] at hcost
    simpa only [Real.rpow_one] using hcost
  have hmeas : Measurable fun z : B × B => ‖z.1 - z.2‖ := by
    have hc : Continuous fun z : B × B => ‖z.1 - z.2‖ := by fun_prop
    exact hc.measurable
  have hfin : ∫⁻ z : B × B, ENNReal.ofReal ‖z.1 - z.2‖ ∂π < ⊤ :=
    lt_of_lt_of_le hcost1 le_top
  have hnn : 0 ≤ᵐ[π] (fun z : B × B => ‖z.1 - z.2‖) := ae_of_all _ fun z => norm_nonneg _
  have hint : Integrable (fun z : B × B => ‖z.1 - z.2‖) π :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩
  have hint_eq : ∫ z, ‖z.1 - z.2‖ ∂π = (∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable
  have hbound : ∫ z, ‖z.1 - z.2‖ ∂π ≤ d + η := by
    rw [hint_eq]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hcost1.le
  exact ⟨π, hprob, hπc.1, hπc.2, hint, hbound⟩

/-- Approximate `W_2`-coupling with real second moment: if `W_2(P,Q) ≤ d` then for every
`η > 0` there is a probability coupling `π` of `P` and `Q` with integrable squared cost and
`∫ ‖x-y‖^2 dπ ≤ (d + η)^2`. -/
theorem fp81s21_exists_coupling_of_W2_le {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℝ} (hd : 0 ≤ d) (hW : HRS.wassersteinE 2 P Q ≤ ENNReal.ofReal d)
    {η : ℝ} (hη : 0 < η) :
    ∃ π : Measure (B × B), IsProbabilityMeasure π ∧ π.map Prod.fst = P ∧ π.map Prod.snd = Q ∧
      Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π ∧
        ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ (d + η) ^ 2 := by
  have hdη : 0 ≤ d + η := by linarith
  have hlt : HRS.wassersteinE 2 P Q < ENNReal.ofReal (d + η) :=
    lt_of_le_of_lt hW ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨π, hπc, hcost⟩ := fp81s21_exists_coupling_of_wassersteinE_lt 2 P Q hlt
  have hprob : IsProbabilityMeasure π := HRS.IsCoupling.isProbabilityMeasure hπc
  have hL : ∫⁻ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π
      < ENNReal.ofReal ((d + η) ^ 2) := by
    have h2 : ((∫⁻ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)
        < (ENNReal.ofReal (d + η)) ^ (2 : ℝ) :=
      ENNReal.rpow_lt_rpow hcost (by norm_num)
    have e2 : (1 : ℝ) / 2 * 2 = 1 := by norm_num
    rw [← ENNReal.rpow_mul, e2, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hdη (by norm_num), Real.rpow_two] at h2
    exact h2
  have hsq : ∀ z : B × B, ‖z.1 - z.2‖ ^ (2 : ℝ) = ‖z.1 - z.2‖ ^ 2 := fun z => Real.rpow_two _
  have hL' : ∫⁻ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π
      < ENNReal.ofReal ((d + η) ^ 2) := by
    simpa only [hsq] using hL
  have hmeas2 : Measurable fun z : B × B => ‖z.1 - z.2‖ ^ 2 := by
    have hc : Continuous fun z : B × B => ‖z.1 - z.2‖ ^ 2 := by fun_prop
    exact hc.measurable
  have hfin : ∫⁻ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π < ⊤ :=
    lt_of_lt_of_le hL' le_top
  have h0sq : 0 ≤ᵐ[π] (fun z : B × B => ‖z.1 - z.2‖ ^ 2) := ae_of_all _ fun z => sq_nonneg _
  have hint : Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π :=
    ⟨hmeas2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0sq).2 hfin⟩
  have hint_eq : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π).toReal :=
    integral_eq_lintegral_of_nonneg_ae h0sq hmeas2.aestronglyMeasurable
  have hbound : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ (d + η) ^ 2 := by
    rw [hint_eq]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL'.le
  exact ⟨π, hprob, hπc.1, hπc.2, hint, hbound⟩

#print axioms fp81s21_exists_coupling_of_wassersteinE_lt
#print axioms fp81s21_isProbabilityMeasure_of_isCoupling
#print axioms fp81s21_exists_coupling_of_W1_le
#print axioms fp81s21_exists_coupling_of_W2_le

end HRS.Fp81.S21

end
