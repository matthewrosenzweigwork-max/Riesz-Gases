import Mathlib

/-!
# Q12, Peyre part 1: sharp second-derivative bound for a composition
-/

noncomputable section

open Set

namespace HRS.Uniform.Q12

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma q12_fderiv_comp_eq {Φ : Y → Z} {c : X → Y} (hΦ : ContDiff ℝ 2 Φ) (hc : ContDiff ℝ 2 c) :
    fderiv ℝ (Φ ∘ c) = fun y => (fderiv ℝ Φ (c y)).comp (fderiv ℝ c y) := by
  funext y
  exact fderiv_comp y (hΦ.differentiable (by norm_num) _) (hc.differentiable (by norm_num) _)

lemma q12_fderiv2_comp_le {Φ : Y → Z} {c : X → Y} (hΦ : ContDiff ℝ 2 Φ) (hc : ContDiff ℝ 2 c)
    (x : X) {A₁ A₂ K₁ K₂ : ℝ} (hA₁ : ‖fderiv ℝ Φ (c x)‖ ≤ A₁)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ Φ) (c x)‖ ≤ A₂) (hK₁ : ‖fderiv ℝ c x‖ ≤ K₁)
    (hK₂ : ‖fderiv ℝ (fderiv ℝ c) x‖ ≤ K₂) :
    ‖fderiv ℝ (fderiv ℝ (Φ ∘ c)) x‖ ≤ A₂ * K₁ ^ 2 + A₁ * K₂ := by
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hc1 : ContDiff ℝ 1 (fderiv ℝ c) := hc.fderiv_right (by norm_num)
  have hdc : DifferentiableAt ℝ (fderiv ℝ c) x := hc1.differentiable one_ne_zero x
  have hdΦ : DifferentiableAt ℝ (fun y => fderiv ℝ Φ (c y)) x := by
    refine DifferentiableAt.comp x (hΦ1.differentiable one_ne_zero _) ?_
    exact hc.differentiable (by norm_num) x
  have hderiv : fderiv ℝ (fun y => fderiv ℝ Φ (c y)) x =
      (fderiv ℝ (fderiv ℝ Φ) (c x)).comp (fderiv ℝ c x) :=
    fderiv_comp x (hΦ1.differentiable one_ne_zero _) (hc.differentiable (by norm_num) x)
  rw [q12_fderiv_comp_eq hΦ hc]
  rw [fderiv_clm_comp hdΦ hdc]
  have hA₁0 : 0 ≤ A₁ := le_trans (norm_nonneg (fderiv ℝ Φ (c x))) hA₁
  have hK₁0 : 0 ≤ K₁ := le_trans (norm_nonneg (fderiv ℝ c x)) hK₁
  have hA₂0 : 0 ≤ A₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) (c x))) hA₂
  have hK₂0 : 0 ≤ K₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ c) x)) hK₂
  have hbd : 0 ≤ A₂ * K₁ ^ 2 + A₁ * K₂ := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hbd fun h => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun k => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, hderiv]
  have e1 : ‖(fderiv ℝ Φ (c x)) ((fderiv ℝ (fderiv ℝ c) x h) k)‖ ≤ A₁ * K₂ * ‖h‖ * ‖k‖ := by
    calc _ ≤ ‖fderiv ℝ Φ (c x)‖ * ‖(fderiv ℝ (fderiv ℝ c) x h) k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ A₁ * (‖fderiv ℝ (fderiv ℝ c) x h‖ * ‖k‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ A₁ * ((‖fderiv ℝ (fderiv ℝ c) x‖ * ‖h‖) * ‖k‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ A₁ * ((K₂ * ‖h‖) * ‖k‖) := by gcongr
      _ = _ := by ring
  have e2 : ‖((fderiv ℝ (fderiv ℝ Φ) (c x)) ((fderiv ℝ c x) h)) ((fderiv ℝ c x) k)‖ ≤
      A₂ * K₁ ^ 2 * ‖h‖ * ‖k‖ := by
    calc _ ≤ ‖(fderiv ℝ (fderiv ℝ Φ) (c x)) ((fderiv ℝ c x) h)‖ * ‖(fderiv ℝ c x) k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ Φ) (c x)‖ * ‖(fderiv ℝ c x) h‖) * ‖(fderiv ℝ c x) k‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (A₂ * (K₁ * ‖h‖)) * (K₁ * ‖k‖) := by
          have h1 : ‖(fderiv ℝ c x) h‖ ≤ K₁ * ‖h‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
          have h2 : ‖(fderiv ℝ c x) k‖ ≤ K₁ * ‖k‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
          gcongr
      _ = _ := by ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ A₁ * K₂ * ‖h‖ * ‖k‖ + A₂ * K₁ ^ 2 * ‖h‖ * ‖k‖ := add_le_add e1 e2
    _ = _ := by ring

end HRS.Uniform.Q12
