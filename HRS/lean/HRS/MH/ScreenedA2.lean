import HRS.MH.ScreenedDefs

/-!
# Packet A2 of `B:lem:screened` (S.B.4): cell Cauchy-Schwarz.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma a2_sqrt_mul_self (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

lemma a2_sq_sqrt (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy-Schwarz for `ℝ≥0∞` lintegrals, squared form. -/
lemma a2_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, a2_sq_sqrt, a2_sq_sqrt]

/-- `‖f‖_{L²}² = ∫⁻ ‖f‖ₑ²` in `ℝ≥0∞`. -/
lemma a2_sq_eLpNorm {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (hf : Measurable f) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact a2_sq_sqrt _

/-- Per-cell estimate: `(∫_Q |ψ|)² ≤ |Q| · ‖1_Q ψ‖₂²`. -/
lemma a2_cell (Q : Set (Euc d)) (hQm : MeasurableSet Q) (ψ : Euc d → ℝ) (hψ : Measurable ψ) :
    (∫⁻ y in Q, ‖ψ y‖ₑ) ^ 2 ≤ volume Q * (eLpNorm (Q.indicator ψ) 2 volume) ^ 2 := by
  have hind : ∀ x, Q.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖Q.indicator ψ x‖ₑ =
      Q.indicator (fun y => ‖ψ y‖ₑ) x := by
    intro x
    by_cases hx : x ∈ Q <;> simp [Set.indicator, hx]
  have hsq : ∀ x, (Q.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ 2 = Q.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ Q <;> simp [Set.indicator, hx]
  have hQf : Measurable (Q.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hQm
  have hg : Measurable (fun x => ‖Q.indicator ψ x‖ₑ) :=
    (hψ.indicator hQm).enorm
  have h := a2_cs volume (Q.indicator (fun _ => (1 : ℝ≥0∞))) (fun x => ‖Q.indicator ψ x‖ₑ) hQf hg
  have hA : ∫⁻ a, Q.indicator (fun _ => (1 : ℝ≥0∞)) a ^ 2 ∂volume = volume Q := by
    simp only [hsq]
    exact lintegral_indicator_one hQm
  have hB : ∫⁻ a, Q.indicator (fun y => ‖ψ y‖ₑ) a ∂volume = ∫⁻ y in Q, ‖ψ y‖ₑ :=
    lintegral_indicator hQm _
  simp only [hind] at h
  rw [hA, hB] at h
  rw [a2_sq_eLpNorm volume (Q.indicator ψ) (hψ.indicator hQm)]
  exact h

lemma a2_weighted_cs {ι : Type*} [Countable ι] (β e : ι → ℝ≥0∞) :
    (∑' i, β i * e i) ^ 2 ≤ (∑' i, β i) * ∑' i, β i * e i ^ 2 := by
  letI : MeasurableSpace ι := ⊤
  haveI : DiscreteMeasurableSpace ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have h := a2_cs (Measure.count : Measure ι) (fun i => β i ^ (1 / 2 : ℝ))
    (fun i => β i ^ (1 / 2 : ℝ) * e i) measurable_from_top (measurable_from_top.mul measurable_from_top)
  have e1 : ∀ i, β i ^ (1 / 2 : ℝ) * (β i ^ (1 / 2 : ℝ) * e i) = β i * e i := by
    intro i
    rw [← mul_assoc, a2_sqrt_mul_self]
  have e2 : ∀ i, (β i ^ (1 / 2 : ℝ)) ^ 2 = β i := fun i => a2_sq_sqrt _
  have e3 : ∀ i, (β i ^ (1 / 2 : ℝ) * e i) ^ 2 = β i * e i ^ 2 := by
    intro i
    rw [mul_pow, a2_sq_sqrt]
  simp only [e1, e2, e3] at h
  rw [lintegral_count' measurable_from_top, lintegral_count' measurable_from_top,
    lintegral_count' measurable_from_top] at h
  exact h

theorem cell_cs_proof {ι : Type*} [Countable ι] (Q : ι → Set (Euc d)) (hQ : (⋃ i, Q i) = univ)
    (hQm : ∀ i, MeasurableSet (Q i)) (V : ℝ≥0∞) (hV : ∀ i, volume (Q i) ≤ V) (β : ι → ℝ≥0∞)
    (G : Euc d → ℝ≥0∞) (hG : ∀ i, ∀ y ∈ Q i, G y ≤ β i) (ψ : Euc d → ℝ) (hψ : Measurable ψ) :
    (∫⁻ y, G y * ‖ψ y‖ₑ) ^ 2 ≤
      ((∑' i, β i) * V) * ∑' i, β i * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2 := by
  have hA : ∫⁻ y, G y * ‖ψ y‖ₑ ≤ ∑' i, β i * ∫⁻ y in Q i, ‖ψ y‖ₑ := by
    rw [← setLIntegral_univ, ← hQ]
    refine (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum fun i => ?_)
    calc ∫⁻ y in Q i, G y * ‖ψ y‖ₑ ≤ ∫⁻ y in Q i, β i * ‖ψ y‖ₑ :=
          setLIntegral_mono' (hQm i) fun y hy => mul_le_mul_of_nonneg_right (hG i y hy) (by positivity)
      _ = β i * ∫⁻ y in Q i, ‖ψ y‖ₑ := lintegral_const_mul _ hψ.enorm
  have hcell : ∀ i, (∫⁻ y in Q i, ‖ψ y‖ₑ) ^ 2 ≤ V * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2 :=
    fun i => (a2_cell (Q i) (hQm i) ψ hψ).trans (mul_le_mul_of_nonneg_right (hV i) (by positivity))
  have hsum : ∑' i, β i * (V * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2) =
      V * ∑' i, β i * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2 := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun i => by ring
  calc (∫⁻ y, G y * ‖ψ y‖ₑ) ^ 2 ≤ (∑' i, β i * ∫⁻ y in Q i, ‖ψ y‖ₑ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hA 2
    _ ≤ (∑' i, β i) * ∑' i, β i * (∫⁻ y in Q i, ‖ψ y‖ₑ) ^ 2 := a2_weighted_cs β _
    _ ≤ (∑' i, β i) * ∑' i, β i * (V * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2) :=
        mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun i => mul_le_mul_of_nonneg_left (hcell i) (by positivity)) (by positivity)
    _ = ((∑' i, β i) * V) * ∑' i, β i * (eLpNorm ((Q i).indicator ψ) 2 volume) ^ 2 := by
        rw [hsum]; ring

end HRS.MH.Screened
