import HRS.MC.S7PIDTMom
import HRS.MC.S7PIDNMain

/-!
# Packet PI-D, sub-packet T (part 11): the abstract expectation bounds

Pure probability: bounds for `|E M[a, b]|` and `|E M[a, b] - E M[a₀, b₀]|` from second-moment bounds of majorants.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {Ω : Type*} [MeasurableSpace Ω]

lemma S7PIDT_bil_le (M : X [×2]→L[ℝ] ℝ) (a b : X) : ‖M ![a, b]‖ ≤ ‖M‖ * (‖a‖ * ‖b‖) := by
  calc ‖M ![a, b]‖ ≤ ‖M‖ * ∏ i, ‖(![a, b] : Fin 2 → X) i‖ := M.le_opNorm _
    _ = ‖M‖ * (‖a‖ * ‖b‖) := by simp [Fin.prod_univ_two]

/-- from `(x)² ≤ y²`, `0 ≤ y` conclude `x ≤ y` -/
lemma S7PIDT_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (le_abs_self x).trans (abs_le_of_sq_le_sq h hy)

theorem S7PIDT_B1 (P : Measure Ω) [IsProbabilityMeasure P] (M : X [×2]→L[ℝ] ℝ) (a b : Ω → X)
    (C κ κ' W : ℝ) (hC : 0 ≤ C) (hW : 0 ≤ W) (hW2 : W ^ 2 = κ * κ') (S S' : Ω → ℝ)
    (hSm : Measurable S) (hSm' : Measurable S') (hS0 : ∀ ω, 0 ≤ S ω) (hS0' : ∀ ω, 0 ≤ S' ω)
    (ha : ∀ ω, ‖a ω‖ ≤ C * S ω) (hb : ∀ ω, ‖b ω‖ ≤ C * S' ω)
    (hSi : Integrable (fun ω => S ω ^ 2) P) (hSi' : Integrable (fun ω => S' ω ^ 2) P)
    (hSI : ∫ ω, S ω ^ 2 ∂P ≤ 162 * κ) (hSI' : ∫ ω, S' ω ^ 2 ∂P ≤ 162 * κ') :
    |∫ ω, M ![a ω, b ω] ∂P| ≤ 162 * (‖M‖ * C ^ 2 * W) := by
  obtain ⟨hint, hcs⟩ := S7PIDT_cs hSm hSm' hSi hSi' hSI hSI'
  have hpt : ∀ ω, ‖M ![a ω, b ω]‖ ≤ ‖M‖ * C ^ 2 * (S ω * S' ω) := by
    intro ω
    refine (S7PIDT_bil_le M _ _).trans ?_
    have h1 : ‖a ω‖ * ‖b ω‖ ≤ (C * S ω) * (C * S' ω) :=
      mul_le_mul (ha ω) (hb ω) (norm_nonneg _) (mul_nonneg hC (hS0 ω))
    calc ‖M‖ * (‖a ω‖ * ‖b ω‖) ≤ ‖M‖ * ((C * S ω) * (C * S' ω)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖M‖ * C ^ 2 * (S ω * S' ω) := by ring
  have h1 : ‖∫ ω, M ![a ω, b ω] ∂P‖ ≤ ∫ ω, ‖M‖ * C ^ 2 * (S ω * S' ω) ∂P :=
    norm_integral_le_of_norm_le (hint.const_mul _) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at h1
  have h2 : ∫ ω, S ω * S' ω ∂P ≤ 162 * W := by
    refine S7PIDT_le_of_sq (by positivity) ?_
    have hκκ : 0 ≤ κ * κ' := by rw [← hW2]; positivity
    calc (∫ ω, S ω * S' ω ∂P) ^ 2 ≤ (162 * κ) * (162 * κ') := hcs
      _ = (162 * W) ^ 2 := by rw [mul_pow, hW2]; ring
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  calc ‖M‖ * C ^ 2 * ∫ ω, S ω * S' ω ∂P ≤ ‖M‖ * C ^ 2 * (162 * W) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 162 * (‖M‖ * C ^ 2 * W) := by ring

theorem S7PIDT_B2 (P : Measure Ω) [IsProbabilityMeasure P] (M : X [×2]→L[ℝ] ℝ) (a b a₀ b₀ : Ω → X)
    (C : ℝ) (hC : 0 ≤ C) (A1 A2 A3 A4 W1 W2 : ℝ) (hW1 : 0 ≤ W1) (hW2 : 0 ≤ W2)
    (hW1s : W1 ^ 2 = A1 * A4) (hW2s : W2 ^ 2 = A3 * A2)
    (S S' δ δ' : Ω → ℝ)
    (hSm : Measurable S) (hSm' : Measurable S') (hδm : Measurable δ) (hδm' : Measurable δ')
    (hS0 : ∀ ω, 0 ≤ S ω) (hS0' : ∀ ω, 0 ≤ S' ω) (hδ0 : ∀ ω, 0 ≤ δ ω) (hδ0' : ∀ ω, 0 ≤ δ' ω)
    (hb : ∀ ω, ‖b ω‖ ≤ C * S' ω) (ha₀ : ∀ ω, ‖a₀ ω‖ ≤ C * S ω)
    (hab : ∀ ω, ‖a ω - a₀ ω‖ ≤ C * δ ω) (hbb : ∀ ω, ‖b ω - b₀ ω‖ ≤ C * δ' ω)
    (hSi : Integrable (fun ω => S ω ^ 2) P) (hSi' : Integrable (fun ω => S' ω ^ 2) P)
    (hδi : Integrable (fun ω => δ ω ^ 2) P) (hδi' : Integrable (fun ω => δ' ω ^ 2) P)
    (hδI : ∫ ω, δ ω ^ 2 ∂P ≤ A1) (hδI' : ∫ ω, δ' ω ^ 2 ∂P ≤ A3)
    (hSI : ∫ ω, S ω ^ 2 ∂P ≤ A2) (hSI' : ∫ ω, S' ω ^ 2 ∂P ≤ A4)
    (hi1 : Integrable (fun ω => M ![a ω, b ω]) P) (hi2 : Integrable (fun ω => M ![a₀ ω, b₀ ω]) P) :
    |∫ ω, M ![a ω, b ω] ∂P - ∫ ω, M ![a₀ ω, b₀ ω] ∂P| ≤ ‖M‖ * C ^ 2 * (W1 + W2) := by
  obtain ⟨hint1, hcs1⟩ := S7PIDT_cs hδm hSm' hδi hSi' hδI hSI'
  obtain ⟨hint2, hcs2⟩ := S7PIDT_cs hSm hδm' hSi hδi' hSI hδI'
  have hpt : ∀ ω, ‖M ![a ω, b ω] - M ![a₀ ω, b₀ ω]‖ ≤
      ‖M‖ * C ^ 2 * ((δ ω * S' ω) + (S ω * δ' ω)) := by
    intro ω
    have e1 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_left M (a ω - a₀ ω) (a₀ ω) (b ω)
    have e2 := HRS.MC.Sec7.S7PIDN.S7PIDN_elem_add_right M (a₀ ω) (b₀ ω) (b ω - b₀ ω)
    rw [sub_add_cancel] at e1
    rw [add_sub_cancel] at e2
    have e : M ![a ω, b ω] - M ![a₀ ω, b₀ ω] =
        M ![a ω - a₀ ω, b ω] + M ![a₀ ω, b ω - b₀ ω] := by
      rw [e1, e2]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 := S7PIDT_bil_le M (a ω - a₀ ω) (b ω)
    have h2 := S7PIDT_bil_le M (a₀ ω) (b ω - b₀ ω)
    have h1' : ‖a ω - a₀ ω‖ * ‖b ω‖ ≤ (C * δ ω) * (C * S' ω) :=
      mul_le_mul (hab ω) (hb ω) (norm_nonneg _) (mul_nonneg hC (hδ0 ω))
    have h2' : ‖a₀ ω‖ * ‖b ω - b₀ ω‖ ≤ (C * S ω) * (C * δ' ω) :=
      mul_le_mul (ha₀ ω) (hbb ω) (norm_nonneg _) (mul_nonneg hC (hS0 ω))
    have hM := norm_nonneg M
    nlinarith [mul_le_mul_of_nonneg_left h1' hM, mul_le_mul_of_nonneg_left h2' hM]
  have hsub : ∫ ω, M ![a ω, b ω] ∂P - ∫ ω, M ![a₀ ω, b₀ ω] ∂P =
      ∫ ω, (M ![a ω, b ω] - M ![a₀ ω, b₀ ω]) ∂P := (integral_sub hi1 hi2).symm
  rw [hsub]
  have hg : Integrable (fun ω => ‖M‖ * C ^ 2 * ((δ ω * S' ω) + (S ω * δ' ω))) P :=
    (hint1.add hint2).const_mul _
  have h3 : ‖∫ ω, (M ![a ω, b ω] - M ![a₀ ω, b₀ ω]) ∂P‖ ≤
      ∫ ω, ‖M‖ * C ^ 2 * ((δ ω * S' ω) + (S ω * δ' ω)) ∂P :=
    norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at h3
  refine h3.trans ?_
  rw [integral_const_mul, integral_add hint1 hint2]
  have hA1 : 0 ≤ A1 := (integral_nonneg fun ω => sq_nonneg _).trans hδI
  have hA4 : 0 ≤ A4 := (integral_nonneg fun ω => sq_nonneg _).trans hSI'
  have h4 : ∫ ω, δ ω * S' ω ∂P ≤ W1 :=
    S7PIDT_le_of_sq hW1 (hcs1.trans (le_of_eq hW1s.symm))
  have h5 : ∫ ω, S ω * δ' ω ∂P ≤ W2 :=
    S7PIDT_le_of_sq hW2 (hcs2.trans (le_of_eq (by rw [hW2s]; ring)))
  have hM : 0 ≤ ‖M‖ * C ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add h4 h5) hM

end HRS.MC.Sec7.S7PIDT

end
