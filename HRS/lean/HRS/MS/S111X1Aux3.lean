import HRS.MS.S111X1Aux2

/-!
# S11.1 X1, part 3: the noise covariance on classical adjoint solutions
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- If a classical adjoint solution exists, `r ↦ propagatorW C r t φ` is one. -/
theorem x1_prop_classical {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW C t φ f) :
    IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ) := by
  have : (fun r => propagatorW C r t φ) = h.choose := by
    funext r; unfold propagatorW; rw [dif_pos h]
  rw [this]
  exact h.choose_spec

theorem x1_pair_intOn {C : WholeCoeff d} {t t' T0 : ℝ} {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (hh : IsClassicalAdjointW C t' ψ h) {ρ : Euc d → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : T0 ≤ t) (h2 : T0 ≤ t') :
    IntegrableOn (fun s => ∫ x, inner ℝ (gradient (f s) x) (gradient (h s) x) * ρ x)
      (Set.Icc (0 : ℝ) T0) :=
  (x1_pair_continuousOn hf hh hρi hρ0 h1 h2).integrableOn_Icc

/-- the noise covariance is bounded by the energies -/
theorem x1_noise_sq_le {C : WholeCoeff d} {r t : ℝ} {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C r ψ f) (hh : IsClassicalAdjointW C t φ h) {ρ : Euc d → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    (∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (f s) x) (gradient (h s) x) * ρ x) ^ 2 ≤
      (∫ s in Set.Icc (0 : ℝ) r, ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * ρ x) *
        (∫ s in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (h s) x) (gradient (h s) x) * ρ x) := by
  have hrm : min r t ≤ r := min_le_left _ _
  have htm : min r t ≤ t := min_le_right _ _
  have hcs := x1_cs hρ0 (fun s x => gradient (f s) x) (fun s x => gradient (h s) x) (min r t)
    (fun s hs => x1_pair_integrable hf hf hρi hρ0 ⟨hs.1, hs.2.trans hrm⟩ ⟨hs.1, hs.2.trans hrm⟩)
    (fun s hs => x1_pair_integrable hh hh hρi hρ0 ⟨hs.1, hs.2.trans htm⟩ ⟨hs.1, hs.2.trans htm⟩)
    (fun s hs => x1_pair_integrable hf hh hρi hρ0 ⟨hs.1, hs.2.trans hrm⟩ ⟨hs.1, hs.2.trans htm⟩)
    (x1_pair_intOn hf hf hρi hρ0 hrm hrm) (x1_pair_intOn hh hh hρi hρ0 htm htm)
    (x1_pair_intOn hf hh hρi hρ0 hrm htm)
  refine hcs.trans ?_
  have m1 : (∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * ρ x) ≤
      ∫ s in Set.Icc (0 : ℝ) r, ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * ρ x := by
    refine setIntegral_mono_set (x1_pair_intOn hf hf hρi hρ0 le_rfl le_rfl) ?_
      (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right hrm))
    exact Filter.Eventually.of_forall fun s => integral_nonneg fun x =>
      mul_nonneg real_inner_self_nonneg (hρ0 x)
  have m2 : (∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (h s) x) (gradient (h s) x) * ρ x) ≤
      ∫ s in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (h s) x) (gradient (h s) x) * ρ x := by
    refine setIntegral_mono_set (x1_pair_intOn hh hh hρi hρ0 le_rfl le_rfl) ?_
      (Filter.Eventually.of_forall (Set.Icc_subset_Icc_right htm))
    exact Filter.Eventually.of_forall fun s => integral_nonneg fun x =>
      mul_nonneg real_inner_self_nonneg (hρ0 x)
  have n1 : 0 ≤ ∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (f s) x) (gradient (f s) x) * ρ x :=
    setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x =>
      mul_nonneg real_inner_self_nonneg (hρ0 x)
  exact mul_le_mul m1 m2 (setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x =>
      mul_nonneg real_inner_self_nonneg (hρ0 x)) (n1.trans m1)

/-- linearity of the pairing in the first solution -/
theorem x1_pair_lin {C : WholeCoeff d} {r t : ℝ} {ψ₁ ψ₂ φ : Euc d → ℝ} {f₁ f₂ h : ℝ → Euc d → ℝ}
    (hf₁ : IsClassicalAdjointW C r ψ₁ f₁) (hf₂ : IsClassicalAdjointW C r ψ₂ f₂)
    (hh : IsClassicalAdjointW C t φ h) {ρ : Euc d → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (c : ℝ) :
    (∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x,
      inner ℝ (gradient (fun y => f₁ s y + c * f₂ s y) x) (gradient (h s) x) * ρ x) =
    (∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (f₁ s) x) (gradient (h s) x) * ρ x) +
      c * ∫ s in Set.Icc (0 : ℝ) (min r t), ∫ x, inner ℝ (gradient (f₂ s) x) (gradient (h s) x) * ρ x := by
  have hrm : min r t ≤ r := min_le_left _ _
  have htm : min r t ≤ t := min_le_right _ _
  have hin : ∀ s ∈ Set.Icc (0 : ℝ) (min r t),
      (∫ x, inner ℝ (gradient (fun y => f₁ s y + c * f₂ s y) x) (gradient (h s) x) * ρ x) =
        (∫ x, inner ℝ (gradient (f₁ s) x) (gradient (h s) x) * ρ x) +
          c * ∫ x, inner ℝ (gradient (f₂ s) x) (gradient (h s) x) * ρ x := by
    intro s hs
    have hs1 : s ∈ Set.Icc (0 : ℝ) r := ⟨hs.1, hs.2.trans hrm⟩
    have hs2 : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1, hs.2.trans htm⟩
    have e : ∀ x, inner ℝ (gradient (fun y => f₁ s y + c * f₂ s y) x) (gradient (h s) x) * ρ x =
        inner ℝ (gradient (f₁ s) x) (gradient (h s) x) * ρ x +
          c * (inner ℝ (gradient (f₂ s) x) (gradient (h s) x) * ρ x) := by
      intro x
      rw [x1_gradient_add_smul c ((hf₁.c2 s hs1).differentiable (by norm_num) x)
        ((hf₂.c2 s hs1).differentiable (by norm_num) x), inner_add_left, inner_smul_left]
      simp only [conj_trivial]
      ring
    simp_rw [e]
    rw [integral_add (x1_pair_integrable hf₁ hh hρi hρ0 hs1 hs2)
      ((x1_pair_integrable hf₂ hh hρi hρ0 hs1 hs2).const_mul c), integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Icc hin,
    integral_add (x1_pair_intOn hf₁ hh hρi hρ0 hrm htm) ((x1_pair_intOn hf₂ hh hρi hρ0 hrm htm).const_mul c),
    integral_const_mul]

end HRS.MS.S111X1
