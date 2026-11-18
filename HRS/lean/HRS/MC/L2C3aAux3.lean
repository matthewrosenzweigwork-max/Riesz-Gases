import HRS.MC.L2C3aAux2

/-!
# Packet L2C-3a, helper 3: pointwise bound for `𝓛_{ρ₁} f - 𝓛_{ρ₂} f`

`|𝓛_{ρ₁} f(x) - 𝓛_{ρ₂} f(x)| ≤ ε (N |∇f(x)| + ∫ |∇g(z)| |∇f(x-z)| dz)`
when `|ρ₁ - ρ₂| ≤ ε`, `N = ∫ |∇g|`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L2C3a

variable {d : ℕ}

theorem l2c3a_diff_bound (D : DynData d) (hd : 2 ≤ d) (hM : D.M = -1) (hs : D.s + 1 < d)
    {ρ₁ ρ₂ : Torus d → ℝ} (hm₁ : Measurable ρ₁) (hm₂ : Measurable ρ₂) {B₁ B₂ ε : ℝ}
    (hB₁ : ∀ x, |ρ₁ x| ≤ B₁) (hB₂ : ∀ x, |ρ₂ x| ≤ B₂) (hε : ∀ x, |ρ₁ x - ρ₂ x| ≤ ε)
    {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (x : Torus d) :
    |backwardGenerator D ρ₁ f x - backwardGenerator D ρ₂ f x| ≤
      ε * ((∫ z, ‖periodicRieszGrad d D.s z‖) * ‖Torus.grad f x‖ +
        ∫ z, ‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖) := by
  obtain ⟨C, hG, hGi⟩ := l2c3a_kernel hd D.hs0 hs
  have hgc : Continuous (Torus.grad f) := HRS.PDE.MFLinear.continuous_grad hf
  obtain ⟨Bg, hBg0, hBg⟩ := l2c3a_bdd_of_cont _ hgc
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε (0 : Torus d))
  have hmδ : Measurable fun y => ρ₁ y - ρ₂ y := hm₁.sub hm₂
  set N := ∫ z, ‖periodicRieszGrad d D.s z‖ with hN
  rw [l2c3a_bg_plain D hd hM hs hm₁ hB₁ hf x, l2c3a_bg_plain D hd hM hs hm₂ hB₂ hf x]
  have i1 := l2c3a_integrable_smul hm₁ hB₁ hG.meas hGi x
  have i2 := l2c3a_integrable_smul hm₂ hB₂ hG.meas hGi x
  have iδ := l2c3a_integrable_smul hmδ hε hG.meas hGi x
  have hJ : ∀ (ρ : Torus d → ℝ), Measurable ρ → ∀ {B : ℝ}, (∀ y, |ρ y| ≤ B) →
      Integrable (fun z => ρ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)) := by
    intro ρ hρ B hB
    refine Integrable.mono' (hGi.norm.const_mul (B * Bg)) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h1 : Measurable fun z => ρ (x - z) := hρ.comp (measurable_const.sub measurable_id)
      have h2 : Measurable fun z => Torus.grad f (x - z) :=
        hgc.measurable.comp (measurable_const.sub measurable_id)
      exact (h1.mul (h2.inner hG.meas)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h3 := abs_real_inner_le_norm (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)
      calc |ρ (x - z)| * |inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)|
          ≤ B * (‖Torus.grad f (x - z)‖ * ‖periodicRieszGrad d D.s z‖) :=
            mul_le_mul (hB (x - z)) h3 (abs_nonneg _) ((abs_nonneg _).trans (hB (x - z)))
        _ ≤ B * (Bg * ‖periodicRieszGrad d D.s z‖) := by
            have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (0 : Torus d))
            gcongr
            exact hBg _
        _ = B * Bg * ‖periodicRieszGrad d D.s z‖ := by ring
  have j1 := hJ ρ₁ hm₁ hB₁
  have j2 := hJ ρ₂ hm₂ hB₂
  have jδ := hJ _ hmδ hε
  have hI : (∫ z, ρ₁ (x - z) • periodicRieszGrad d D.s z) -
      (∫ z, ρ₂ (x - z) • periodicRieszGrad d D.s z) =
      ∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) • periodicRieszGrad d D.s z := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [sub_smul]
  have hJ' : (∫ z, ρ₁ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)) -
      (∫ z, ρ₂ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)) =
      ∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z) := by
    rw [← integral_sub j1 j2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have e : D.invβ * Torus.laplacian f x +
      inner ℝ (-(∫ z, ρ₁ (x - z) • periodicRieszGrad d D.s z) - Torus.grad D.V x) (Torus.grad f x) +
      (∫ z, ρ₁ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)) -
      (D.invβ * Torus.laplacian f x +
      inner ℝ (-(∫ z, ρ₂ (x - z) • periodicRieszGrad d D.s z) - Torus.grad D.V x) (Torus.grad f x) +
      (∫ z, ρ₂ (x - z) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z))) =
      inner ℝ (-(∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) • periodicRieszGrad d D.s z)) (Torus.grad f x) +
      ∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z) := by
    rw [← hI, ← hJ', ← sub_eq_zero]
    have : inner ℝ (-(∫ z, ρ₁ (x - z) • periodicRieszGrad d D.s z) - Torus.grad D.V x) (Torus.grad f x) -
        inner ℝ (-(∫ z, ρ₂ (x - z) • periodicRieszGrad d D.s z) - Torus.grad D.V x) (Torus.grad f x) =
        inner ℝ (-((∫ z, ρ₁ (x - z) • periodicRieszGrad d D.s z) -
          (∫ z, ρ₂ (x - z) • periodicRieszGrad d D.s z))) (Torus.grad f x) := by
      rw [← inner_sub_left]; congr 1; abel
    linarith
  rw [e]
  have b1 : |inner ℝ (-(∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) • periodicRieszGrad d D.s z)) (Torus.grad f x)| ≤
      ε * N * ‖Torus.grad f x‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_neg]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [hN, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
      (hGi.norm.const_mul ε) (Filter.Eventually.of_forall fun z => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hε _) (norm_nonneg _)
  have hint2 : Integrable (fun z => ε * (‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖)) := by
    refine Integrable.mono' (hGi.norm.const_mul (ε * Bg)) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 : Measurable fun z => ‖Torus.grad f (x - z)‖ :=
        (hgc.measurable.comp (measurable_const.sub measurable_id)).norm
      exact (measurable_const.mul (hG.meas.norm.mul h2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ε * (‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖)
          ≤ ε * (‖periodicRieszGrad d D.s z‖ * Bg) := by gcongr; exact hBg _
        _ = ε * Bg * ‖periodicRieszGrad d D.s z‖ := by ring
  have b2 : |∫ z, (ρ₁ (x - z) - ρ₂ (x - z)) * inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)| ≤
      ε * ∫ z, ‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖ := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hint2
      (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul]
    have h3 := abs_real_inner_le_norm (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)
    calc |ρ₁ (x - z) - ρ₂ (x - z)| * |inner ℝ (Torus.grad f (x - z)) (periodicRieszGrad d D.s z)|
        ≤ ε * (‖Torus.grad f (x - z)‖ * ‖periodicRieszGrad d D.s z‖) :=
          mul_le_mul (hε _) h3 (abs_nonneg _) hε0
      _ = ε * (‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖) := by ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε * N * ‖Torus.grad f x‖ + ε * ∫ z, ‖periodicRieszGrad d D.s z‖ * ‖Torus.grad f (x - z)‖ :=
        add_le_add b1 b2
    _ = _ := by ring

end HRS.MC.L2C3a
