import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1

/-!
# CoercLower B3a: convolution bounds (packets P06a, P06b)

Proofs of the statements in `HRS/MH/CoercLowerSpec.lean`, copied verbatim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

theorem clb3a_integrable_shift (hd : 1 ≤ d) {f φ ρ : Euc d → ℝ} {a Λ : ℝ} (hf : Measurable f)
    (hlo : ∀ z, z ≠ 0 → -a ≤ f z) (hup : ∀ z, z ≠ 0 → f z ≤ φ z)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ : Integrable φ) (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (x : Euc d) :
    Integrable (fun y => f (x - y) * ρ y) := by
  have hρi : Integrable ρ := isProbDensity_integrable hρ
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  have h1 : Integrable (fun y => (φ (x - y) + |a|) * ρ y) := by
    have e : (fun y => (φ (x - y) + |a|) * ρ y) = fun y => φ (x - y) * ρ y + |a| * ρ y := by
      funext y; ring
    rw [e]
    refine Integrable.add ?_ (hρi.const_mul _)
    refine Integrable.mono' ((hφ.comp_sub_left x).const_mul Λ) ?_ ?_
    · exact ((hφ.comp_sub_left x).aestronglyMeasurable).mul hρi.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hφ0 _) (hρ.nonneg y))]
      exact mul_le_mul_of_nonneg_left (hΛ y) (hφ0 _) |>.trans_eq' rfl |>.trans (by
        nlinarith [hφ0 (x - y), hΛ y, hρ.nonneg y])
  refine Integrable.mono' h1 ?_ ?_
  · exact (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hρi.aestronglyMeasurable
  · have hne : ∀ᵐ y : Euc d ∂volume, x - y ≠ 0 := by
      have := ae_ne_zero hd (d := d)
      have h2 := (Measure.measurePreserving_sub_left (volume : Measure (Euc d)) x).quasiMeasurePreserving.ae this
      exact h2
    filter_upwards [hne] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
    refine mul_le_mul_of_nonneg_right ?_ (hρ.nonneg y)
    rw [abs_le]
    constructor
    · have := hlo _ hy
      have := neg_abs_le a
      nlinarith [hφ0 (x - y), abs_nonneg a, le_abs_self a]
    · have := hup _ hy
      nlinarith [abs_nonneg a]

/-- [P06a] A kernel `f` with `-a ≤ f ≤ φ` off `0`, `φ ≥ 0` integrable: convolution bounds. -/
theorem conv_bounds_of_bounds (hd : 1 ≤ d) {f φ ρ : Euc d → ℝ} {a Λ : ℝ} (hf : Measurable f)
    (ha : 0 ≤ a) (hlo : ∀ z, z ≠ 0 → -a ≤ f z) (hup : ∀ z, z ≠ 0 → f z ≤ φ z)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ : Integrable φ) (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) :
    (∀ x, Integrable (fun y => f (x - y) * ρ y)) ∧
      (∀ x, -a ≤ HRS.Whole.convFun f ρ x ∧ HRS.Whole.convFun f ρ x ≤ Λ * ∫ z, φ z) ∧
      Integrable (fun x => ρ x * HRS.Whole.convFun f ρ x) ∧ -a ≤ energyDens f ρ := by
  have hρi : Integrable ρ := isProbDensity_integrable hρ
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  have hint := clb3a_integrable_shift hd hf hlo hup hφ0 hφ hρ hΛ
  have hne : ∀ x : Euc d, ∀ᵐ y : Euc d ∂volume, x - y ≠ 0 := fun x => by
    have := ae_ne_zero hd (d := d)
    exact (Measure.measurePreserving_sub_left (volume : Measure (Euc d)) x).quasiMeasurePreserving.ae
      this
  have hbd : ∀ x, -a ≤ HRS.Whole.convFun f ρ x ∧ HRS.Whole.convFun f ρ x ≤ Λ * ∫ z, φ z := by
    intro x
    constructor
    · have h1 : ∫ y, (-a) * ρ y = -a := by
        rw [integral_const_mul, hρ.integral_one, mul_one]
      rw [← h1]
      refine integral_mono_ae (hρi.const_mul _) (hint x) ?_
      filter_upwards [hne x] with y hy
      exact mul_le_mul_of_nonneg_right (hlo _ hy) (hρ.nonneg y)
    · have h1 : ∫ y, Λ * φ (x - y) = Λ * ∫ z, φ z := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun z => φ z) volume x]
      rw [← h1]
      refine integral_mono_ae (hint x) ((hφ.comp_sub_left x).const_mul _) ?_
      filter_upwards [hne x] with y hy
      calc f (x - y) * ρ y ≤ φ (x - y) * ρ y :=
            mul_le_mul_of_nonneg_right (hup _ hy) (hρ.nonneg y)
        _ ≤ φ (x - y) * Λ := mul_le_mul_of_nonneg_left (hΛ y) (hφ0 _)
        _ = Λ * φ (x - y) := mul_comm _ _
  have hmeas : AEStronglyMeasurable (HRS.Whole.convFun f ρ) volume := by
    have hm : Measurable (fun p : Euc d × Euc d => f (p.1 - p.2) * ρ p.2) :=
      (hf.comp (measurable_fst.sub measurable_snd)).mul (hρ.measurable.comp measurable_snd)
    exact (hm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hint2 : Integrable (fun x => ρ x * HRS.Whole.convFun f ρ x) := by
    refine Integrable.mono' (hρi.const_mul (max a (Λ * ∫ z, φ z))) (hρi.aestronglyMeasurable.mul hmeas)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (hρ.nonneg x)
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hbd x
    exact ⟨by linarith [le_max_left a (Λ * ∫ z, φ z)], h2.trans (le_max_right _ _)⟩
  refine ⟨hint, hbd, hint2, ?_⟩
  have h1 : ∫ x, ρ x * (-a) = -a := by
    rw [integral_mul_const, hρ.integral_one, one_mul]
  unfold energyDens
  rw [← h1]
  refine integral_mono (hρi.mul_const _) hint2 fun x => ?_
  exact mul_le_mul_of_nonneg_left (hbd x).1 (hρ.nonneg x)

/-- [P06b] Lower bound for the tail form (`i ≠ j` terms need injectivity of `X`). -/
theorem Qform_lower_of_bounds (hd : 1 ≤ d) {f φ ρ : Euc d → ℝ} {a Λ : ℝ} (hf : Measurable f)
    (ha : 0 ≤ a) (hlo : ∀ z, z ≠ 0 → -a ≤ f z) (hup : ∀ z, z ≠ 0 → f z ≤ φ z)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ : Integrable φ) (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) (hX : Function.Injective X) :
    f 0 / N - 2 * a - 2 * Λ * ∫ z, φ z ≤ Qform f X ρ := by
  obtain ⟨-, hbd, -, hen⟩ := conv_bounds_of_bounds hd hf ha hlo hup hφ0 hφ hρ hΛ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hrow : ∀ i : Fin N, (f 0 + a) - N * a ≤ ∑ j, f (X i - X j) := by
    intro i
    have h1 : ∀ j ∈ (Finset.univ : Finset (Fin N)),
        (if i = j then f 0 + a else 0) - a ≤ f (X i - X j) := by
      intro j _
      by_cases hij : i = j
      · subst hij; simp
      · have hne : X i - X j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hX h))
        have := hlo _ hne
        simp [hij, this]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum h1)
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq]
  have hsum : N * ((f 0 + a) - N * a) ≤ ∑ i, ∑ j, f (X i - X j) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hrow i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hconv : ∑ i, HRS.Whole.convFun f ρ (X i) ≤ N * (Λ * ∫ z, φ z) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => (hbd (X i)).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  unfold Qform
  have hA : f 0 / N - a ≤ 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, f (X i - X j) := by
    have h2 : f 0 / N - a ≤ 1 / (N : ℝ) ^ 2 * (N * ((f 0 + a) - N * a)) := by
      have : 1 / (N : ℝ) ^ 2 * (N * ((f 0 + a) - N * a)) = f 0 / N + a / N - a := by
        field_simp
      rw [this]
      have : 0 ≤ a / N := div_nonneg ha hNpos.le
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hB : 2 / (N : ℝ) * ∑ i, HRS.Whole.convFun f ρ (X i) ≤ 2 * (Λ * ∫ z, φ z) := by
    calc 2 / (N : ℝ) * ∑ i, HRS.Whole.convFun f ρ (X i)
        ≤ 2 / (N : ℝ) * (N * (Λ * ∫ z, φ z)) :=
          mul_le_mul_of_nonneg_left hconv (by positivity)
      _ = 2 * (Λ * ∫ z, φ z) := by field_simp
  linarith

end HRS.MH.CoercLower
