import HRS.Commutator.Whole.XLIAux17

/-!
# X-LI part 18: the high-output square function bound
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma rpow_add_le_two {s : ℝ} (hs : 0 ≤ s) (a b : ℝ≥0∞) :
    (a + b) ^ s ≤ 2 ^ s * (a ^ s + b ^ s) := by
  have h1 : a + b ≤ 2 * max a b := by
    calc a + b ≤ max a b + max a b := add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max a b := by ring
  calc (a + b) ^ s ≤ (2 * max a b) ^ s := ENNReal.rpow_le_rpow h1 hs
    _ = 2 ^ s * (max a b) ^ s := ENNReal.mul_rpow_of_nonneg _ _ hs
    _ ≤ 2 ^ s * (a ^ s + b ^ s) := by
        gcongr
        rcases le_total a b with h | h
        · rw [max_eq_right h]; exact le_add_self
        · rw [max_eq_left h]; exact le_self_add

section High

variable (α : ℝ)

lemma YY_meas (φ ψ : SchwartzMap 𝔼 ℂ) (k : ℤ) : Measurable (YY α φ ψ k) := by
  have : YY α φ ψ k =
      fun x => CvP k (fun y => ∑' n : ℤ, wgt α n * hh α φ ψ (k + n) y) x :=
    funext (YY_eq_CvP α φ ψ k)
  rw [this]
  exact CvP_measurable k (Measurable.ennreal_tsum fun n =>
    measurable_const.mul (hh_meas α φ ψ (k + n)))

/-- **high-output square function bound** in terms of the majorant square functions -/
lemma HIGH [Nontrivial 𝔼] (hd : 1 ≤ d) (hα : 0 < α) {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f g : SchwartzMap 𝔼 ℂ,
      ∫⁻ x, (∑' k : ℤ, if 1 ≤ k then
          ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0) ^ s ≤
        C * ((∫⁻ x, QQ α f g x ^ s) + ∫⁻ x, QQ α g f x ^ s) := by
  obtain ⟨C₁, hC₁, hPB⟩ := PB (d := d) α
  obtain ⟨C₂, hC₂, hYY⟩ := YY_sq_bound α hd hα hs
  have hs0 : 0 < s := by linarith
  set T : ℝ≥0∞ := 2 * C₁ ^ 2 with hT
  have hTne : T ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hC₁)
  refine ⟨(T ^ s * 2 ^ s) * C₂, ?_, fun f g => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs0.le hTne)
      (ENNReal.rpow_ne_top_of_nonneg hs0.le (by simp))) hC₂
  have hpt : ∀ x, (∑' k : ℤ, if 1 ≤ k then
      ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0) ≤
      T * (∑' k : ℤ, YY α f g k x ^ 2 + ∑' k : ℤ, YY α g f k x ^ 2) := by
    intro x
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    split_ifs with hk
    · have h1 := hPB f g k hk x
      calc ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2
          ≤ (C₁ * (YY α f g k x + YY α g f k x)) ^ 2 := by gcongr
        _ = C₁ ^ 2 * (YY α f g k x + YY α g f k x) ^ 2 := by ring
        _ ≤ C₁ ^ 2 * (2 * (YY α f g k x ^ 2 + YY α g f k x ^ 2)) := by
            gcongr; exact add_sq_le_two _ _
        _ = T * (YY α f g k x ^ 2 + YY α g f k x ^ 2) := by rw [hT]; ring
    · exact zero_le
  have hmeasA : Measurable (fun x => (∑' k : ℤ, YY α f g k x ^ 2) ^ s) :=
    (Measurable.ennreal_tsum fun k => (YY_meas α f g k).pow_const 2).pow_const s
  calc ∫⁻ x, (∑' k : ℤ, if 1 ≤ k then
          ‖cv (symK rho k) ⇑(Fm α (prodS f g)) x‖ₑ ^ 2 else 0) ^ s
      ≤ ∫⁻ x, (T * (∑' k : ℤ, YY α f g k x ^ 2 + ∑' k : ℤ, YY α g f k x ^ 2)) ^ s :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hs0.le
    _ ≤ ∫⁻ x, T ^ s * (2 ^ s * ((∑' k : ℤ, YY α f g k x ^ 2) ^ s +
          (∑' k : ℤ, YY α g f k x ^ 2) ^ s)) := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le]
        gcongr
        exact rpow_add_le_two hs0.le _ _
    _ = T ^ s * (2 ^ s * ((∫⁻ x, (∑' k : ℤ, YY α f g k x ^ 2) ^ s) +
          ∫⁻ x, (∑' k : ℤ, YY α g f k x ^ 2) ^ s)) := by
        have h2 : Measurable (fun x => 2 ^ s * ((∑' k : ℤ, YY α f g k x ^ 2) ^ s +
            (∑' k : ℤ, YY α g f k x ^ 2) ^ s)) :=
          measurable_const.mul (hmeasA.add
            ((Measurable.ennreal_tsum fun k => (YY_meas α g f k).pow_const 2).pow_const s))
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le hTne),
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le (by simp)),
          lintegral_add_left hmeasA]
    _ ≤ ((T ^ s * 2 ^ s) * C₂) * ((∫⁻ x, QQ α f g x ^ s) + ∫⁻ x, QQ α g f x ^ s) := by
        have h1 := hYY f g
        have h2 := hYY g f
        calc T ^ s * (2 ^ s * ((∫⁻ x, (∑' k : ℤ, YY α f g k x ^ 2) ^ s) +
              ∫⁻ x, (∑' k : ℤ, YY α g f k x ^ 2) ^ s))
            ≤ T ^ s * (2 ^ s * ((C₂ * ∫⁻ x, QQ α f g x ^ s) + C₂ * ∫⁻ x, QQ α g f x ^ s)) :=
              mul_le_mul_right (mul_le_mul_right (add_le_add h1 h2) _) _
          _ = _ := by ring

end High

end HRS.Commutator.Whole.XLI
