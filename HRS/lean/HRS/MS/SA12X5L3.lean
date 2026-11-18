import HRS.MS.SA12X5L0

/-!
# S.A.12 X5 LOC3: `jetSq` of a combination `f₁ + f₂ - f₃` and of a constant multiple
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x5_loc_pd_comb {f₁ f₂ f₃ : Euc d → ℝ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (h₃ : ContDiff ℝ ∞ f₃) {n : ℕ} (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f₁ y + f₂ y - f₃ y) x =
      partialDeriv idx f₁ x + partialDeriv idx f₂ x - partialDeriv idx f₃ x := by
  unfold partialDeriv
  have e : (fun y => f₁ y + f₂ y - f₃ y) = (f₁ + f₂) - f₃ := rfl
  have h12 : ContDiff ℝ ∞ (f₁ + f₂) := h₁.add h₂
  rw [e, iteratedFDeriv_sub_apply (h12.contDiffAt.of_le (by exact_mod_cast le_top))
    (h₃.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_add_apply (h₁.contDiffAt.of_le (by exact_mod_cast le_top))
    (h₂.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp

theorem sa12x5_loc_pd_const_mul {f : Euc d → ℝ} (h : ContDiff ℝ ∞ f) (c : ℝ) {n : ℕ}
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => c * f y) x = c * partialDeriv idx f x := by
  unfold partialDeriv
  have e : (fun y => c * f y) = fun y => c • f y := by funext y; simp [smul_eq_mul]
  rw [e, iteratedFDeriv_const_smul_apply' (h.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp

theorem sa12x5_jetSq_const_mul' (m : ℕ) (w : Euc d → ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    jetSq m w (fun x => c * f x) = c ^ 2 * jetSq m w f :=
  sa12x5_jetSq_const_mul m w f c (fun idx x => sa12x5_loc_pd_const_mul hf c idx x)

theorem sa12x5_jetSq_sum_le (m : ℕ) {w : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {f₁ f₂ f₃ : Euc d → ℝ} (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂) (h₃ : ContDiff ℝ ∞ f₃) :
    jetSq m w (fun x => f₁ x + f₂ x - f₃ x) ≤ 3 * (jetSq m w f₁ + jetSq m w f₂ + jetSq m w f₃) := by
  have key : ∀ {n : ℕ} (idx : Fin n → Fin d),
      ∫ x, (w x * partialDeriv idx (fun y => f₁ y + f₂ y - f₃ y) x) ^ 2 ≤
        3 * ((∫ x, (w x * partialDeriv idx f₁ x) ^ 2) + (∫ x, (w x * partialDeriv idx f₂ x) ^ 2) +
          (∫ x, (w x * partialDeriv idx f₃ x) ^ 2)) := by
    intro n idx
    have i1 := sa12x5_loc_integrable hw hwc (sa12z3_pd_contDiff_inf h₁ idx).continuous
    have i2 := sa12x5_loc_integrable hw hwc (sa12z3_pd_contDiff_inf h₂ idx).continuous
    have i3 := sa12x5_loc_integrable hw hwc (sa12z3_pd_contDiff_inf h₃ idx).continuous
    have e3 : ∫ x, 3 * ((w x * partialDeriv idx f₁ x) ^ 2 + (w x * partialDeriv idx f₂ x) ^ 2 +
        (w x * partialDeriv idx f₃ x) ^ 2) = 3 * ((∫ x, (w x * partialDeriv idx f₁ x) ^ 2) +
          (∫ x, (w x * partialDeriv idx f₂ x) ^ 2) + (∫ x, (w x * partialDeriv idx f₃ x) ^ 2)) := by
      have i12 : Integrable (fun x => (w x * partialDeriv idx f₁ x) ^ 2 + (w x * partialDeriv idx f₂ x) ^ 2) :=
        i1.add i2
      rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2]
    rw [← e3]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
      (((i1.add i2).add i3).const_mul 3) (Eventually.of_forall fun x => ?_)
    simp only [sa12x5_loc_pd_comb h₁ h₂ h₃ idx x]
    nlinarith [sq_nonneg (w x * partialDeriv idx f₁ x - w x * partialDeriv idx f₂ x),
      sq_nonneg (w x * partialDeriv idx f₁ x + w x * partialDeriv idx f₃ x),
      sq_nonneg (w x * partialDeriv idx f₂ x + w x * partialDeriv idx f₃ x)]
  unfold jetSq
  calc _ ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        3 * ((∫ x, (w x * partialDeriv idx f₁ x) ^ 2) + (∫ x, (w x * partialDeriv idx f₂ x) ^ 2) +
          (∫ x, (w x * partialDeriv idx f₃ x) ^ 2)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun idx _ => key idx) (Nat.cast_nonneg _)
    _ = _ := by
        have hj : ∀ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
            3 * ((∫ x, (w x * partialDeriv idx f₁ x) ^ 2) + (∫ x, (w x * partialDeriv idx f₂ x) ^ 2) +
              (∫ x, (w x * partialDeriv idx f₃ x) ^ 2)) =
            3 * ((Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx f₁ x) ^ 2)) +
              (Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx f₂ x) ^ 2)) +
              (Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx f₃ x) ^ 2))) := by
          intro j _
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
          ring
        rw [Finset.sum_congr rfl hj, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]

end HRS.MH.AdjointRd.Phase2SA12X5
