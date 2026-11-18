import HRS.Uniform.Q54cAux45

/-!
# Q54c, part 46: pathwise domination of the difference of two Riesz processes by path suprema
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q48b HRS.Uniform.Q54

variable {d : ℕ}

theorem sup_enorm_ne_top {E : Type*} [NormedAddCommGroup E] {T : ℝ} {F : ℝ → E}
    (hF : ContinuousOn F (Set.Icc 0 T)) : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖F t‖ₑ) ≠ ⊤ := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hF
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B)) (iSup₂_le fun t ht => ?_)
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hB t ht)

theorem norm_le_sup_toReal {E : Type*} [NormedAddCommGroup E] {T : ℝ} {F : ℝ → E}
    (hF : ContinuousOn F (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖F t‖ ≤ (⨆ s ∈ Set.Icc (0 : ℝ) T, ‖F s‖ₑ).toReal := by
  have hne := sup_enorm_ne_top hF
  have h1 : ‖F t‖ₑ ≤ ⨆ s ∈ Set.Icc (0 : ℝ) T, ‖F s‖ₑ := le_iSup₂_of_le t ht le_rfl
  rw [← ofReal_norm_eq_enorm] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 h1

variable {a : ℝ}

theorem yelt_dom {P₁ P₂ : PathData d a} {T K₁ K₂ : ℝ} (h₁ : P₁.Spec T K₁) (h₂ : P₂.Spec T K₂)
    {G₁ G₂ : ℝ → NegSobolev d a} (hG₁ : ContinuousOn G₁ (Set.Icc 0 T)) (hG₂ : ContinuousOn G₂ (Set.Icc 0 T))
    {δ δw : ℝ}
    (hy : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖P₁.y t φ σ - P₂.y t φ σ‖ ≤ δ * sobolevNorm (a + 4) φ)
    (hy' : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖P₁.y' t φ σ - P₂.y' t φ σ‖ ≤ δ * sobolevNorm (a + 4) φ)
    (A₁ A₂ : ℝ) (η : NegSobolev d (a + 2))
    (hw : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖A₁ • P₁.w t φ - A₂ • P₂.w t φ‖ ≤ δw * sobolevNorm (a + 4) φ)
    (hδ : 0 ≤ δ) (hδw : 0 ≤ δw) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖P₁.Yelt A₁ η G₁ t - P₂.Yelt A₂ η G₂ t‖ ≤
      (1 + T) * K₁ * (⨆ s ∈ Set.Icc (0 : ℝ) T, ‖G₁ s - G₂ s‖ₑ).toReal +
      (1 + T) * δ * (⨆ s ∈ Set.Icc (0 : ℝ) T, ‖G₂ s‖ₑ).toReal + δw * ‖η‖ := by
  have hGd : ContinuousOn (fun s => G₁ s - G₂ s) (Set.Icc 0 T) := hG₁.sub hG₂
  set D := (⨆ s ∈ Set.Icc (0 : ℝ) T, ‖G₁ s - G₂ s‖ₑ).toReal with hD
  set M := (⨆ s ∈ Set.Icc (0 : ℝ) T, ‖G₂ s‖ₑ).toReal with hM
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  have hM₂ : ∀ σ ∈ Set.Icc 0 T, ‖G₂ σ‖ ≤ M := fun σ hσ => norm_le_sup_toReal hG₂ hσ
  have hDD : ∀ σ ∈ Set.Icc 0 T, ‖G₁ σ - G₂ σ‖ ≤ D := fun σ hσ => norm_le_sup_toReal hGd hσ
  have hM₁ : ∀ σ ∈ Set.Icc 0 T, ‖G₁ σ‖ ≤ M + D := fun σ hσ => by
    calc ‖G₁ σ‖ = ‖G₂ σ + (G₁ σ - G₂ σ)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G₂ σ‖ + ‖G₁ σ - G₂ σ‖ := norm_add_le _ _
      _ ≤ M + D := add_le_add (hM₂ σ hσ) (hDD σ hσ)
  have := Yelt_cmp h₁ h₂ hG₁ hG₂ hM₂ hM₁ hDD hy hy' A₁ A₂ η hw hδ hδw hD0 ht
  refine this.trans (le_of_eq ?_)
  ring

end HRS.Uniform.Q54c
