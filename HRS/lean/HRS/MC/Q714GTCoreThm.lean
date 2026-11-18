import HRS.MC.Q714GTThm

/-!
# Packet GT (row 7.14), the law-level Gaussian Taylor theorem
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.Q714.GT

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- Extraction of a uniform bound of an iterated derivative from `MemCb`. -/
lemma gt_memCb_bound {Φ : B → ℝ} {k : ℕ} (hΦ : MemCb k Φ) {j : ℕ} (hj : j ≤ k) :
    ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hΦ.2 j hj
  exact ⟨M, fun x => hM ⟨x, rfl⟩⟩

theorem gt_core {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (h₁ : IsCenteredGaussian γ₁) (h₂ : IsCenteredGaussian γ₂)
    (Δ : (B [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : B [×2]→L[ℝ] ℝ, Δ M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁)
    (δ : ℝ) (hδ : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ)
    (Φ : B → ℝ) (hΦ : MemCb 4 Φ) (C₂ C₄ : ℝ)
    (hC₂ : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ C₂) (hC₄ : ∀ y, ‖iteratedFDeriv ℝ 4 Φ y‖ ≤ C₄) :
    |∫ z, Φ z ∂γ₂ - ∫ z, Φ z ∂γ₁| ≤ C₂ * δ / 2 ∧
    |∫ z, Φ z ∂γ₂ - ∫ z, Φ z ∂γ₁ - (1 / 2) * ∫ z, Δ (iteratedFDeriv ℝ 2 Φ z) ∂γ₁| ≤
      C₄ * δ ^ 2 / 8 := by
  have hs₁ := gaussian_sqnorm_integrable h₁
  have hs₂ := gaussian_sqnorm_integrable h₂
  obtain ⟨L, hLΔ, hδ0, hLn⟩ := gt_delta_clm hs₁ hs₂ Δ hΔ δ hδ
  have hL : ∀ M : B [×2]→L[ℝ] ℝ, L M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁ :=
    fun M => by rw [hLΔ, hΔ]
  set μ := γ₁.prod γ₂ with hμ
  -- regularity and bounds of `Φ`
  have hΦ4 : ContDiff ℝ 4 Φ := hΦ.1
  have hΦ2 : ContDiff ℝ 2 Φ := hΦ4.of_le (by norm_num)
  obtain ⟨M0', hM0'⟩ := gt_memCb_bound hΦ (j := 0) (by norm_num)
  obtain ⟨M1, hM1⟩ := gt_memCb_bound hΦ (j := 1) (by norm_num)
  obtain ⟨M3, hM3⟩ := gt_memCb_bound hΦ (j := 3) (by norm_num)
  have hM0 : ∀ w, |Φ w| ≤ M0' := fun w => by
    have := hM0' w
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ 0)
  have hC₄0 : 0 ≤ C₄ := (norm_nonneg _).trans (hC₄ 0)
  -- the function `Ψ = Δ ∘ D²Φ`
  set D2 : B → (B [×2]→L[ℝ] ℝ) := iteratedFDeriv ℝ 2 Φ with hD2def
  have hD2 : ContDiff ℝ 2 D2 := hΦ4.iteratedFDeriv_right (i := 2) (m := 2) (by norm_num)
  set Ψ : B → ℝ := fun u => L (D2 u) with hΨdef
  have hΨ : ContDiff ℝ 2 Ψ := L.contDiff.comp hD2
  have hΨΔ : ∀ u, Ψ u = Δ (iteratedFDeriv ℝ 2 Φ u) := fun u => hLΔ _
  have hΨ0 : ∀ w, |Ψ w| ≤ δ * C₂ := fun w => by
    rw [← Real.norm_eq_abs]
    calc ‖L (D2 w)‖ ≤ ‖L‖ * ‖D2 w‖ := L.le_opNorm _
      _ ≤ δ * C₂ := mul_le_mul hLn (hC₂ w) (norm_nonneg _) hδ0
  have hΨj : ∀ j : ℕ, j ≤ 2 → ∀ w, ‖iteratedFDeriv ℝ j Ψ w‖ ≤
      δ * ‖iteratedFDeriv ℝ (2 + j) Φ w‖ := by
    intro j hj w
    have h1 : iteratedFDeriv ℝ j (L ∘ D2) w =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ j D2 w) :=
      L.iteratedFDeriv_comp_left (hD2.contDiffAt) (by exact_mod_cast hj)
    have h2 : iteratedFDeriv ℝ j Ψ w = iteratedFDeriv ℝ j (L ∘ D2) w := rfl
    rw [h2, h1]
    refine (L.norm_compContinuousMultilinearMap_le _).trans ?_
    rw [hD2def, gt_norm_iter_iter]
    exact mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
  have hΨ1 : ∀ w, ‖iteratedFDeriv ℝ 1 Ψ w‖ ≤ δ * M3 := fun w =>
    (hΨj 1 (by norm_num) w).trans (mul_le_mul_of_nonneg_left (hM3 w) hδ0)
  have hΨ2 : ∀ w, ‖iteratedFDeriv ℝ 2 Ψ w‖ ≤ δ * C₄ := fun w =>
    (hΨj 2 le_rfl w).trans (mul_le_mul_of_nonneg_left (hC₄ w) hδ0)
  -- the two interpolation derivatives
  set f : ℝ → ℝ := fun θ => ∫ q, Φ (gtPt θ q) ∂μ with hf
  set fΨ : ℝ → ℝ := fun θ => ∫ q, Ψ (gtPt θ q) ∂μ with hfΨ
  have hIΦ := fun θ => gt_interp h₁ h₂ L hL hLn hΦ2 hM0 hM1 hC₂ θ
  have hIΨ := fun θ => gt_interp h₁ h₂ L hL hLn hΨ hΨ0 hΨ1 hΨ2 θ
  have hfd : ∀ θ, HasDerivAt f (Real.sin θ * Real.cos θ * fΨ θ) θ := fun θ => (hIΦ θ).1
  have hfΨd : ∀ θ, HasDerivAt fΨ
      (Real.sin θ * Real.cos θ * ∫ q, L (iteratedFDeriv ℝ 2 Ψ (gtPt θ q)) ∂μ) θ :=
    fun θ => (hIΨ θ).1
  have hfΨb : ∀ θ, |fΨ θ| ≤ δ * C₂ := fun θ => (hIΦ θ).2
  have hfΨ'b : ∀ θ, |∫ q, L (iteratedFDeriv ℝ 2 Ψ (gtPt θ q)) ∂μ| ≤ δ * (δ * C₄) :=
    fun θ => (hIΨ θ).2
  -- endpoints
  obtain ⟨e1, e2⟩ := gt_endpoints (γ₁ := γ₁) (γ₂ := γ₂) hΦ2.continuous hM0
  obtain ⟨e3, -⟩ := gt_endpoints (γ₁ := γ₁) (γ₂ := γ₂) hΨ.continuous hΨ0
  have hf0 : f 0 = ∫ z, Φ z ∂γ₁ := e1
  have hfπ : f (Real.pi / 2) = ∫ z, Φ z ∂γ₂ := e2
  have hfΨ0 : fΨ 0 = ∫ z, Ψ z ∂γ₁ := e3
  have hint : ∫ z, Ψ z ∂γ₁ = ∫ z, Δ (iteratedFDeriv ℝ 2 Φ z) ∂γ₁ := by
    simp_rw [hΨΔ]
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- first order
  have first : |f (Real.pi / 2) - f 0| ≤ C₂ * δ / 2 := by
    have key := gt_cmp_abs (f := f) (f' := fun θ => Real.sin θ * Real.cos θ * fΨ θ)
      (g := fun θ => (δ * C₂ / 2) * Real.sin θ ^ 2)
      (g' := fun θ => 2 * (δ * C₂ / 2) * Real.sin θ * Real.cos θ) hfd
      (fun θ => gt_hasDerivAt_sin_sq _ θ) hπ (fun θ hθ => by
        have hsc := gt_sin_cos_nonneg hθ.1 hθ.2
        rw [abs_mul, abs_of_nonneg hsc]
        have := hfΨb θ
        calc Real.sin θ * Real.cos θ * |fΨ θ| ≤ Real.sin θ * Real.cos θ * (δ * C₂) :=
              mul_le_mul_of_nonneg_left this hsc
          _ = _ := by ring)
    simp only [Real.sin_pi_div_two, Real.sin_zero] at key
    refine key.trans (le_of_eq ?_)
    ring
  refine ⟨by rw [← hfπ, ← hf0]; exact first, ?_⟩
  -- second order
  set A : ℝ := fΨ 0 with hA
  set K' : ℝ := δ * (δ * C₄) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hΨdev : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |fΨ θ - A| ≤ (K' / 2) * Real.sin θ ^ 2 := by
    intro θ hθ
    have key := gt_cmp_abs (f := fΨ)
      (f' := fun θ => Real.sin θ * Real.cos θ * ∫ q, L (iteratedFDeriv ℝ 2 Ψ (gtPt θ q)) ∂μ)
      (g := fun θ => (K' / 2) * Real.sin θ ^ 2)
      (g' := fun θ => 2 * (K' / 2) * Real.sin θ * Real.cos θ) hfΨd
      (fun θ => gt_hasDerivAt_sin_sq _ θ) hθ.1 (fun φ hφ => by
        have hsc := gt_sin_cos_nonneg hφ.1 (hφ.2.trans hθ.2)
        rw [abs_mul, abs_of_nonneg hsc]
        calc Real.sin φ * Real.cos φ * |∫ q, L (iteratedFDeriv ℝ 2 Ψ (gtPt φ q)) ∂μ|
            ≤ Real.sin φ * Real.cos φ * K' := mul_le_mul_of_nonneg_left (hfΨ'b φ) hsc
          _ = _ := by ring)
    simp only [Real.sin_zero] at key
    refine key.trans (le_of_eq ?_)
    ring
  have hkd : ∀ θ, HasDerivAt (fun θ => f θ - (A / 2) * Real.sin θ ^ 2)
      (Real.sin θ * Real.cos θ * fΨ θ - 2 * (A / 2) * Real.sin θ * Real.cos θ) θ :=
    fun θ => (hfd θ).sub (gt_hasDerivAt_sin_sq _ θ)
  have second := gt_cmp_abs (f := fun θ => f θ - (A / 2) * Real.sin θ ^ 2)
    (f' := fun θ => Real.sin θ * Real.cos θ * fΨ θ - 2 * (A / 2) * Real.sin θ * Real.cos θ)
    (g := fun θ => (K' / 8) * Real.sin θ ^ 4)
    (g' := fun θ => 4 * (K' / 8) * Real.sin θ ^ 3 * Real.cos θ) hkd
    (fun θ => gt_hasDerivAt_sin_four _ θ) hπ (fun θ hθ => by
      have hsc := gt_sin_cos_nonneg hθ.1 hθ.2
      have e : Real.sin θ * Real.cos θ * fΨ θ - 2 * (A / 2) * Real.sin θ * Real.cos θ =
          Real.sin θ * Real.cos θ * (fΨ θ - A) := by ring
      rw [e, abs_mul, abs_of_nonneg hsc]
      calc Real.sin θ * Real.cos θ * |fΨ θ - A|
          ≤ Real.sin θ * Real.cos θ * ((K' / 2) * Real.sin θ ^ 2) :=
            mul_le_mul_of_nonneg_left (hΨdev θ hθ) hsc
        _ = _ := by ring)
  simp only [Real.sin_pi_div_two, Real.sin_zero] at second
  rw [hfπ, hf0] at second
  rw [← hint, ← hfΨ0]
  refine le_trans (le_of_eq ?_) (second.trans (le_of_eq ?_))
  · congr 1
    rw [hA]; ring
  · rw [hK']; ring

end HRS.MC.Q714.GT

end
