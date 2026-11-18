import HRS.MS.R2WinErrAux2

/-!
# S10.4 packet E2a': `featureForm` of a bounded measurable feature is a bounded bilinear form

`s104_featureForm_clm`: for a finite measure `ν` and measurable features with `‖Γ_a(x)‖ ≤ B`, the integrals
`featureForm m T q Γ ν u v` are the values of a continuous bilinear form `KSpace d m T →L KSpace d m T →L ℝ`
(this is the existence of the forms `Bt` of `r2_window_errors` (a), part of its conclusion).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2WinErr

open HRS.Whole

variable {d : ℕ}

section Form

variable {m T : ℝ}

theorem s104_integrable_pair {n : ℕ} (Γ : Fin n → Euc d → KSpace d m T) (ν : Measure (Euc d))
    [IsFiniteMeasure ν] {B : ℝ} (hΓm : ∀ a, Measurable (Γ a)) (hΓb : ∀ a x, ‖Γ a x‖ ≤ B)
    (a : Fin n) (u v : KSpace d m T) :
    Integrable (fun x => inner ℝ (Γ a x) u * inner ℝ (Γ a x) v) ν := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hΓb a 0)
  refine Integrable.of_bound (C := B * ‖u‖ * (B * ‖v‖)) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((hΓm a).inner_const.mul (hΓm a).inner_const).aestronglyMeasurable
  · rw [norm_mul]
    have e1 : ‖inner ℝ (Γ a x) u‖ ≤ B * ‖u‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hΓb a x) (norm_nonneg _))
    have e2 : ‖inner ℝ (Γ a x) v‖ ≤ B * ‖v‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hΓb a x) (norm_nonneg _))
    exact mul_le_mul e1 e2 (norm_nonneg _) (by positivity)

theorem s104_featureForm_clm {n : ℕ} (q : ℝ) (Γ : Fin n → Euc d → KSpace d m T) (ν : Measure (Euc d))
    [IsFiniteMeasure ν] {B : ℝ} (hB : 0 ≤ B) (hΓm : ∀ a, Measurable (Γ a)) (hΓb : ∀ a x, ‖Γ a x‖ ≤ B) :
    ∃ F : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ, ∀ u v, F u v = featureForm m T q Γ ν u v := by
  have hint := s104_integrable_pair Γ ν hΓm hΓb
  let f : KSpace d m T →ₗ[ℝ] KSpace d m T →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => featureForm m T q Γ ν u v)
      (fun u u' v => by
        unfold featureForm
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← integral_add (hint a u v) (hint a u' v)]
        congr 1; ext x
        rw [inner_add_right]; ring)
      (fun c u v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        have h : ∀ a, ∫ x, inner ℝ (Γ a x) (c • u) * inner ℝ (Γ a x) v ∂ν =
            c * ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν := fun a => by
          rw [← integral_const_mul]; congr 1; ext x; rw [inner_smul_right]; ring
        unfold featureForm
        simp_rw [h]
        rw [← Finset.mul_sum]; ring)
      (fun u v v' => by
        unfold featureForm
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← integral_add (hint a u v) (hint a u v')]
        congr 1; ext x
        rw [inner_add_right]; ring)
      (fun c u v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        have h : ∀ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) (c • v) ∂ν =
            c * ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν := fun a => by
          rw [← integral_const_mul]; congr 1; ext x; rw [inner_smul_right]; ring
        unfold featureForm
        simp_rw [h]
        rw [← Finset.mul_sum]; ring)
  have hf : ∀ u v, f u v = featureForm m T q Γ ν u v := fun u v => rfl
  have hbd : ∀ u v, ‖f u v‖ ≤ (2 * |q| * n * B ^ 2 * ν.real Set.univ) * ‖u‖ * ‖v‖ := by
    intro u v
    rw [hf]
    unfold featureForm
    have h1 : ∀ a : Fin n, ‖∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν‖ ≤
        (B * ‖u‖ * (B * ‖v‖)) * ν.real Set.univ := by
      intro a
      refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      have e1 : ‖inner ℝ (Γ a x) u‖ ≤ B * ‖u‖ :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hΓb a x) (norm_nonneg _))
      have e2 : ‖inner ℝ (Γ a x) v‖ ≤ B * ‖v‖ :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hΓb a x) (norm_nonneg _))
      exact mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc 2 * ‖q‖ * ‖∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂ν‖
        ≤ 2 * ‖q‖ * ∑ a : Fin n, ((B * ‖u‖ * (B * ‖v‖)) * ν.real Set.univ) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => h1 a))
            (by positivity)
      _ = (2 * |q| * n * B ^ 2 * ν.real Set.univ) * ‖u‖ * ‖v‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.norm_eq_abs]
          ring
  refine ⟨f.mkContinuous₂ _ hbd, fun u v => ?_⟩
  rw [LinearMap.mkContinuous₂_apply]
  rfl

end Form

end HRS.MS.R2WinErr
