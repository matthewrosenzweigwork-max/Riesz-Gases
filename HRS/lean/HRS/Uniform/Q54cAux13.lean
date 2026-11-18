import HRS.Uniform.Q54cAux12

/-!
# Q54c, part 13: comparison of two pathwise processes
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS

variable {d : ℕ} {a : ℝ}

section Cmp

variable {P₁ P₂ : PathData d a} {T K₁ K₂ : ℝ} (h₁ : P₁.Spec T K₁) (h₂ : P₂.Spec T K₂)
variable {G₁ G₂ : ℝ → NegSobolev d a}

include h₁ h₂

/-- Pathwise comparison of the two Riesz processes. -/
theorem Yelt_cmp {M₂ D δ δw : ℝ} (hG₁ : ContinuousOn G₁ (Set.Icc 0 T)) (hG₂ : ContinuousOn G₂ (Set.Icc 0 T))
    (hM₂ : ∀ σ ∈ Set.Icc 0 T, ‖G₂ σ‖ ≤ M₂) (hM₁ : ∀ σ ∈ Set.Icc 0 T, ‖G₁ σ‖ ≤ M₂ + D)
    (hD : ∀ σ ∈ Set.Icc 0 T, ‖G₁ σ - G₂ σ‖ ≤ D)
    (hy : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖P₁.y t φ σ - P₂.y t φ σ‖ ≤ δ * sobolevNorm (a + 4) φ)
    (hy' : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖P₁.y' t φ σ - P₂.y' t φ σ‖ ≤ δ * sobolevNorm (a + 4) φ)
    (A₁ A₂ : ℝ) (η : NegSobolev d (a + 2))
    (hw : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      ‖A₁ • P₁.w t φ - A₂ • P₂.w t φ‖ ≤ δw * sobolevNorm (a + 4) φ)
    (hδ : 0 ≤ δ) (hδw : 0 ≤ δw) (hD0 : 0 ≤ D) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ‖P₁.Yelt A₁ η G₁ t - P₂.Yelt A₂ η G₂ t‖ ≤
      (1 + T) * (K₁ * D + M₂ * δ) + ‖η‖ * δw := by
  have hT := h₁.hT
  have hK₁ := h₁.hK
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0 ⟨le_rfl, hT⟩)
  set B : ℝ := (1 + T) * (K₁ * D + M₂ * δ) + ‖η‖ * δw with hB
  have hB0 : 0 ≤ B := by positivity
  have hH1 := lam_rieszHyp h₁ hG₁ hM₁ A₁ η ht
  have hH2 := lam_rieszHyp h₂ hG₂ hM₂ A₂ η ht
  have hmain : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      |P₁.lam A₁ η G₁ t φ - P₂.lam A₂ η G₂ t φ| ≤ B * sobolevNorm (a + 4) φ := by
    intro φ hφ
    set n := sobolevNorm (a + 4) φ with hn
    have hn0 : 0 ≤ n := Real.sqrt_nonneg _
    -- the integrands
    set f₁ : ℝ → ℝ := fun σ => inner ℝ (G₁ σ - G₂ σ) (P₁.y' t φ σ) with hf₁
    set f₂ : ℝ → ℝ := fun σ => inner ℝ (G₂ σ) (P₁.y' t φ σ - P₂.y' t φ σ) with hf₂
    have hc₁ : ContinuousOn f₁ (Set.Icc 0 t) :=
      ContinuousOn.inner ((hG₁.sub hG₂).mono (Set.Icc_subset_Icc_right ht.2)) (h₁.cont_y' t ht φ hφ)
    have hc₂ : ContinuousOn f₂ (Set.Icc 0 t) :=
      ContinuousOn.inner (hG₂.mono (Set.Icc_subset_Icc_right ht.2))
        ((h₁.cont_y' t ht φ hφ).sub (h₂.cont_y' t ht φ hφ))
    have hi₁ : IntegrableOn f₁ (Set.Icc 0 t) := hc₁.integrableOn_Icc
    have hi₂ : IntegrableOn f₂ (Set.Icc 0 t) := hc₂.integrableOn_Icc
    have hdiffI : (∫ σ in Set.Icc 0 t, inner ℝ (G₁ σ) (P₁.y' t φ σ)) -
        (∫ σ in Set.Icc 0 t, inner ℝ (G₂ σ) (P₂.y' t φ σ)) =
        (∫ σ in Set.Icc 0 t, f₁ σ) + ∫ σ in Set.Icc 0 t, f₂ σ := by
      rw [← integral_add hi₁ hi₂]
      have hi1 : IntegrableOn (fun σ => inner ℝ (G₁ σ) (P₁.y' t φ σ)) (Set.Icc 0 t) :=
        integrand_integrableOn h₁ hG₁ ht hφ
      have hi2 : IntegrableOn (fun σ => inner ℝ (G₂ σ) (P₂.y' t φ σ)) (Set.Icc 0 t) :=
        integrand_integrableOn h₂ hG₂ ht hφ
      rw [← integral_sub hi1 hi2]
      refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      simp only [hf₁, hf₂, inner_sub_left, inner_sub_right]
      ring
    have hb₁ : ‖∫ σ in Set.Icc 0 t, f₁ σ‖ ≤ T * (D * (K₁ * n)) := by
      have hb : ∀ σ ∈ Set.Icc 0 t, ‖f₁ σ‖ ≤ D * (K₁ * n) := by
        intro σ hσ
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hD σ ⟨hσ.1, hσ.2.trans ht.2⟩) (h₁.bd_y' t ht σ hσ φ hφ) (norm_nonneg _) hD0
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hb
      refine this.trans ?_
      rw [Real.volume_real_Icc_of_le ht.1, sub_zero]
      rw [mul_comm (D * (K₁ * n)) t]
      exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
    have hb₂ : ‖∫ σ in Set.Icc 0 t, f₂ σ‖ ≤ T * (M₂ * (δ * n)) := by
      have hb : ∀ σ ∈ Set.Icc 0 t, ‖f₂ σ‖ ≤ M₂ * (δ * n) := by
        intro σ hσ
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (hM₂ σ ⟨hσ.1, hσ.2.trans ht.2⟩) (hy' t ht σ hσ φ hφ) (norm_nonneg _) hM₂0
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hb
      refine this.trans ?_
      rw [Real.volume_real_Icc_of_le ht.1, sub_zero]
      rw [mul_comm (M₂ * (δ * n)) t]
      exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
    have hT1 : |inner ℝ (G₁ t - G₂ t) (P₁.y t φ t)| ≤ D * (K₁ * n) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hD t ht) (h₁.bd_y t ht t ⟨ht.1, le_rfl⟩ φ hφ)
        (norm_nonneg _) hD0)
    have hT2 : |inner ℝ (G₂ t) (P₁.y t φ t - P₂.y t φ t)| ≤ M₂ * (δ * n) :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hM₂ t ht) (hy t ht t ⟨ht.1, le_rfl⟩ φ hφ)
        (norm_nonneg _) hM₂0)
    have hT5 : |A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ| ≤ ‖η‖ * (δw * n) := by
      have e : A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ =
          inner ℝ η (A₁ • P₁.w t φ - A₂ • P₂.w t φ) := by
        unfold PathData.initF
        rw [inner_sub_right, inner_smul_right, inner_smul_right]
      rw [e]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hw t ht φ hφ) (norm_nonneg _))
    have e : P₁.lam A₁ η G₁ t φ - P₂.lam A₂ η G₂ t φ =
        (inner ℝ (G₁ t - G₂ t) (P₁.y t φ t) + inner ℝ (G₂ t) (P₁.y t φ t - P₂.y t φ t)) -
          ((∫ σ in Set.Icc 0 t, f₁ σ) + ∫ σ in Set.Icc 0 t, f₂ σ) +
          (A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ) := by
      unfold PathData.lam PathData.noiseF
      rw [← hdiffI]
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [e]
    have hI1 : |∫ σ in Set.Icc 0 t, f₁ σ| ≤ T * (D * (K₁ * n)) := by
      rw [← Real.norm_eq_abs]; exact hb₁
    have hI2 : |∫ σ in Set.Icc 0 t, f₂ σ| ≤ T * (M₂ * (δ * n)) := by
      rw [← Real.norm_eq_abs]; exact hb₂
    calc _ ≤ |(inner ℝ (G₁ t - G₂ t) (P₁.y t φ t) + inner ℝ (G₂ t) (P₁.y t φ t - P₂.y t φ t)) -
          ((∫ σ in Set.Icc 0 t, f₁ σ) + ∫ σ in Set.Icc 0 t, f₂ σ)| +
          |A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ| := abs_add_le _ _
      _ ≤ (|inner ℝ (G₁ t - G₂ t) (P₁.y t φ t) + inner ℝ (G₂ t) (P₁.y t φ t - P₂.y t φ t)| +
          |(∫ σ in Set.Icc 0 t, f₁ σ) + ∫ σ in Set.Icc 0 t, f₂ σ|) +
          |A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|inner ℝ (G₁ t - G₂ t) (P₁.y t φ t)| + |inner ℝ (G₂ t) (P₁.y t φ t - P₂.y t φ t)|) +
          (|∫ σ in Set.Icc 0 t, f₁ σ| + |∫ σ in Set.Icc 0 t, f₂ σ|)) +
          |A₁ * P₁.initF η t φ - A₂ * P₂.initF η t φ| :=
          add_le_add (add_le_add (abs_add_le _ _) (abs_add_le _ _)) le_rfl
      _ ≤ ((D * (K₁ * n) + M₂ * (δ * n)) + (T * (D * (K₁ * n)) + T * (M₂ * (δ * n)))) + ‖η‖ * (δw * n) := by
          gcongr
      _ = B * n := by rw [hB]; ring
  have hH : RieszHyp (a + 4) B (fun φ => P₁.lam A₁ η G₁ t φ - P₂.lam A₂ η G₂ t φ) := by
    refine ⟨hB0, ?_, hmain, ?_⟩
    · intro φ ψ hφ hψ α β
      rw [hH1.lin φ ψ hφ hψ α β, hH2.lin φ ψ hφ hψ α β]; ring
    · intro c
      rw [hH1.const c, hH2.const c]; ring
  have heq : rieszElt (a + 4) (fun φ => P₁.lam A₁ η G₁ t φ - P₂.lam A₂ η G₂ t φ) =
      P₁.Yelt A₁ η G₁ t - P₂.Yelt A₂ η G₂ t := by
    refine Subtype.ext (funext fun k => ?_)
    have e1 := rieszElt_coord hH k
    have e2 := rieszElt_coord hH1 k
    have e3 := rieszElt_coord hH2 k
    show NegSobolev.coord (rieszElt (a + 4) _) k =
      NegSobolev.coord (P₁.Yelt A₁ η G₁ t - P₂.Yelt A₂ η G₂ t) k
    rw [NegSobolev.coord_sub']
    unfold PathData.Yelt
    rw [e1, e2, e3]; ring
  rw [← heq]
  exact rieszElt_norm_le hH

end Cmp

end HRS.Uniform.Q54c
