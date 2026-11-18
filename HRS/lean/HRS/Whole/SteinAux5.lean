import HRS.Whole.SteinAux4

/-!
# Packet STEIN, auxiliary file 5: bounded smooth test functions, truncation of `C²` functions
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

variable {n : ℕ}

lemma lip_of_fderiv_bound {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : E → G)
    (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ z, ‖fderiv ℝ f z‖ ≤ L) (x y : E) :
    ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (s := Set.univ) (C := L)
    (fun z _ => hf z) (fun z _ => hL z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [norm_sub_rev] using this

lemma trunc_props (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (D₁ D₂ : ℝ)
    (hD₁ : ∀ x, ‖fderiv ℝ F x‖ ≤ D₁) (hD₂ : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ D₂)
    (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ 2 (fun x => atr R (F x)) ∧ (∀ x, |atr R (F x)| ≤ R * (Real.pi / 2)) ∧
      (∀ x, ‖fderiv ℝ (fun y => atr R (F y)) x‖ ≤ D₁) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 (fun y => atr R (F y)) x‖ ≤ D₂ + D₁ ^ 2 / R) := by
  have hD10 : 0 ≤ D₁ := le_trans (norm_nonneg (fderiv ℝ F 0)) (hD₁ 0)
  have hD20 : 0 ≤ D₂ := le_trans (norm_nonneg (iteratedFDeriv ℝ 2 F 0)) (hD₂ 0)
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdF : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hder : ∀ x, fderiv ℝ (fun y => atr R (F y)) x = datr R (F x) • fderiv ℝ F x := by
    intro x
    exact ((hasDerivAt_atr hR.ne' (F x)).comp_hasFDerivAt x (hFd x).hasFDerivAt).fderiv
  have h1 : ∀ x, ‖fderiv ℝ (fun y => atr R (F y)) x‖ ≤ D₁ := by
    intro x
    rw [hder, norm_smul, Real.norm_eq_abs]
    calc |datr R (F x)| * ‖fderiv ℝ F x‖ ≤ 1 * D₁ :=
          mul_le_mul (abs_datr_le _ _) (hD₁ x) (norm_nonneg _) zero_le_one
      _ = D₁ := one_mul _
  have hFlip : ∀ x y, ‖F x - F y‖ ≤ D₁ * ‖x - y‖ := lip_of_fderiv_bound F hFd D₁ hD₁
  have hdFlip : ∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ D₂ * ‖x - y‖ := by
    refine lip_of_fderiv_bound (fderiv ℝ F) hdF D₂ ?_
    intro z
    have : ‖iteratedFDeriv ℝ 1 (fderiv ℝ F) z‖ = ‖iteratedFDeriv ℝ 2 F z‖ := norm_iteratedFDeriv_fderiv (n := 1)
    rw [norm_iteratedFDeriv_one] at this
    rw [this]; exact hD₂ z
  have hlipD : ∀ x y, ‖fderiv ℝ (fun z => atr R (F z)) x - fderiv ℝ (fun z => atr R (F z)) y‖ ≤
      (D₂ + D₁ ^ 2 / R) * ‖x - y‖ := by
    intro x y
    have e : fderiv ℝ (fun z => atr R (F z)) x - fderiv ℝ (fun z => atr R (F z)) y =
        (datr R (F x) - datr R (F y)) • fderiv ℝ F x + datr R (F y) • (fderiv ℝ F x - fderiv ℝ F y) := by
      rw [hder, hder, sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have a1 : |datr R (F x) - datr R (F y)| * ‖fderiv ℝ F x‖ ≤ (D₁ * ‖x - y‖ / R) * D₁ := by
      refine mul_le_mul ?_ (hD₁ x) (norm_nonneg _) (by positivity)
      refine (datr_lip hR _ _).trans ?_
      rw [← Real.norm_eq_abs]
      exact div_le_div_of_nonneg_right (hFlip x y) hR.le
    have a2 : |datr R (F y)| * ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ 1 * (D₂ * ‖x - y‖) :=
      mul_le_mul (abs_datr_le _ _) (hdFlip x y) (norm_nonneg _) zero_le_one
    calc _ ≤ (D₁ * ‖x - y‖ / R) * D₁ + 1 * (D₂ * ‖x - y‖) := add_le_add a1 a2
      _ = (D₂ + D₁ ^ 2 / R) * ‖x - y‖ := by field_simp; ring
  have hL0 : 0 ≤ D₂ + D₁ ^ 2 / R := by positivity
  have hlipW : LipschitzWith ⟨D₂ + D₁ ^ 2 / R, hL0⟩ (fderiv ℝ (fun z => atr R (F z))) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hlipD x y
  refine ⟨(atr_contDiff R).comp hF, fun x => abs_atr_le_bound R _ hR, h1, fun x => ?_⟩
  have h2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ (fun y => atr R (F y))) x‖ =
      ‖iteratedFDeriv ℝ 2 (fun y => atr R (F y)) x‖ := norm_iteratedFDeriv_fderiv (n := 1)
  rw [norm_iteratedFDeriv_one] at h2
  rw [← h2]
  exact norm_fderiv_le_of_lipschitz ℝ hlipW

end HRS.Whole.Stein
