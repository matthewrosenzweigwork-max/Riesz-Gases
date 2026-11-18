import HRS.Uniform.Q12P1
import HRS.Torus.Sobolev

/-!
# Q12, Peyre part 2: the `C²`-test class and its stability under `id + τ w`
-/

noncomputable section

open Set

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- `Φ` is `C²` on `ℝ^d` with `|Φ|, ‖DΦ‖, ‖D²Φ‖ ≤ B`. -/
def C2b (B : ℝ) (Φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ 2 Φ ∧ ∀ y, |Φ y| ≤ B ∧ ‖fderiv ℝ Φ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ Φ) y‖ ≤ B

lemma q12_fderiv_shift {w : Euc d → Euc d} (hw : ContDiff ℝ 2 w) (τ : ℝ) (y : Euc d) :
    fderiv ℝ (fun z => z + τ • w z) y =
      ContinuousLinearMap.id ℝ (Euc d) + τ • fderiv ℝ w y := by
  have hd : DifferentiableAt ℝ w y := hw.differentiable (by norm_num) y
  exact ((hasFDerivAt_id y).add (hd.hasFDerivAt.const_smul τ)).fderiv

lemma q12_fderiv2_shift {w : Euc d → Euc d} (hw : ContDiff ℝ 2 w) (τ : ℝ) (y : Euc d) :
    fderiv ℝ (fderiv ℝ (fun z => z + τ • w z)) y = τ • fderiv ℝ (fderiv ℝ w) y := by
  have e : fderiv ℝ (fun z => z + τ • w z) =
      fun z => ContinuousLinearMap.id ℝ (Euc d) + τ • fderiv ℝ w z := funext (q12_fderiv_shift hw τ)
  rw [e]
  have hd : DifferentiableAt ℝ (fderiv ℝ w) y :=
    (hw.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ w)).differentiable one_ne_zero y
  exact ((hd.hasFDerivAt.const_smul τ).const_add (ContinuousLinearMap.id ℝ (Euc d))).fderiv

lemma q12_C2b_comp {Φ : Euc d → ℝ} {w : Euc d → Euc d} {τ B V₁ V₂ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hΦ : C2b B Φ) (hw : ContDiff ℝ 2 w) (hw1 : ∀ y, ‖fderiv ℝ w y‖ ≤ V₁)
    (hw2 : ∀ y, ‖fderiv ℝ (fderiv ℝ w) y‖ ≤ V₂) :
    C2b (B * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ)) (fun y => Φ (y + τ • w y)) := by
  obtain ⟨hΦc, hΦb⟩ := hΦ
  set c : Euc d → Euc d := fun y => y + τ • w y with hc
  have hc2 : ContDiff ℝ 2 c := contDiff_id.add (hw.const_smul τ)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hΦb 0).1
  have hV₁ : 0 ≤ V₁ := le_trans (norm_nonneg (fderiv ℝ w 0)) (hw1 0)
  have hV₂ : 0 ≤ V₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ w) 0)) (hw2 0)
  have hK₁ : ∀ y, ‖fderiv ℝ c y‖ ≤ 1 + τ * V₁ := fun y => by
    rw [hc, q12_fderiv_shift hw τ y]
    calc _ ≤ ‖ContinuousLinearMap.id ℝ (Euc d)‖ + ‖τ • fderiv ℝ w y‖ := norm_add_le _ _
      _ ≤ 1 + τ * V₁ := by
          rw [norm_smul, Real.norm_of_nonneg hτ]
          exact add_le_add ContinuousLinearMap.norm_id_le (mul_le_mul_of_nonneg_left (hw1 y) hτ)
  have hK₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ c) y‖ ≤ τ * V₂ := fun y => by
    rw [hc, q12_fderiv2_shift hw τ y]
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg hτ]
    exact mul_le_mul_of_nonneg_left (hw2 y) hτ
  have hfac : 1 ≤ 1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ := by
    have : 0 ≤ (2 * V₁ + V₁ ^ 2 + V₂) * τ := by positivity
    linarith
  refine ⟨hΦc.comp hc2, fun y => ⟨?_, ?_, ?_⟩⟩
  · exact ((hΦb (c y)).1).trans (le_mul_of_one_le_right hB0 hfac)
  · have h := q12_fderiv_comp_eq hΦc hc2
    show ‖fderiv ℝ (Φ ∘ c) y‖ ≤ _
    rw [h]
    calc ‖(fderiv ℝ Φ (c y)).comp (fderiv ℝ c y)‖ ≤ ‖fderiv ℝ Φ (c y)‖ * ‖fderiv ℝ c y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * (1 + τ * V₁) := mul_le_mul (hΦb (c y)).2.1 (hK₁ y) (norm_nonneg _) hB0
      _ ≤ B * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          nlinarith [mul_nonneg hV₁ hτ, mul_nonneg (sq_nonneg V₁) hτ, mul_nonneg hV₂ hτ]
  · have := q12_fderiv2_comp_le hΦc hc2 y (hΦb (c y)).2.1 (hΦb (c y)).2.2 (hK₁ y) (hK₂ y)
    show ‖fderiv ℝ (fderiv ℝ (Φ ∘ c)) y‖ ≤ _
    refine this.trans ?_
    have h1 : B * (1 + τ * V₁) ^ 2 + B * (τ * V₂) ≤ B * (1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ) := by
      have : (1 + τ * V₁) ^ 2 + τ * V₂ ≤ 1 + (2 * V₁ + V₁ ^ 2 + V₂) * τ := by
        nlinarith [mul_nonneg hV₁ hτ, mul_nonneg (sq_nonneg V₁) hτ, mul_nonneg hV₂ hτ,
          mul_nonneg (sq_nonneg V₁) (sub_nonneg.2 hτ1), mul_nonneg (mul_nonneg (sq_nonneg V₁) hτ) (sub_nonneg.2 hτ1)]
      nlinarith [mul_le_mul_of_nonneg_left this hB0]
    exact h1

end HRS.Uniform.Q12
