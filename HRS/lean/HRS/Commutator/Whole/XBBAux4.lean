import HRS.Commutator.Whole.XBBAux3

/-!
# Packet XBB, part 4: the Kato–Ponce pair estimates at an arbitrary frequency scale

By dilation from `XBBAux3`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma xbb_cancel {s a b : ℝ≥0∞} (h0 : s ≠ 0) (htop : s ≠ ⊤) (h : s * a ≤ s * b) : a ≤ b :=
  (ENNReal.mul_le_mul_iff_right h0 htop).1 h

lemma xbb_fourier_dil_zero {c : ℝ} (hc : 0 < c) (h : 𝓢(𝔼, ℂ)) {r : ℝ} (hr : ∀ ξ : 𝔼, ‖ξ‖ < r → 𝓕 (⇑h) ξ = 0) (ξ : 𝔼)
    (hξ : ‖ξ‖ < c * r) : 𝓕 (⇑(xbbDil c hc.ne' h)) ξ = 0 := by
  rw [xbb_fourier_dil hc]
  have : ‖c⁻¹ • ξ‖ < r := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, inv_mul_lt_iff₀ hc]
    exact hξ
  rw [hr _ this]; simp

lemma xbb_fourier_dil_zero' {c : ℝ} (hc : 0 < c) (h : 𝓢(𝔼, ℂ)) {r : ℝ} (hr : ∀ ξ : 𝔼, r < ‖ξ‖ → 𝓕 (⇑h) ξ = 0) (ξ : 𝔼)
    (hξ : c * r < ‖ξ‖) : 𝓕 (⇑(xbbDil c hc.ne' h)) ξ = 0 := by
  rw [xbb_fourier_dil hc]
  have : r < ‖c⁻¹ • ξ‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le, lt_inv_mul_iff₀ hc]
    exact hξ
  rw [hr _ this]; simp

/-- the Kato–Ponce estimate for a Fourier-low factor, at scale `μ` -/
lemma xbb_pair_low_scaled (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (μ : ℝ), 0 < μ → ∀ (f Γ : 𝓢(𝔼, ℂ)), (∀ ξ : 𝔼, 4 * μ < ‖ξ‖ → 𝓕 (⇑f) ξ = 0) →
      (∀ ξ : 𝔼, ‖ξ‖ < μ → 𝓕 (⇑Γ) ξ = 0) → ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) →
        xbbN β (fun x => f x * Γ x) ≤ C * ENNReal.ofReal B * xbbN β ⇑Γ := by
  obtain ⟨C, hC, h⟩ := xbb_pair_low hd hβ
  refine ⟨C, hC, fun μ hμ f Γ hf hΓ B hB hfB => ?_⟩
  have hc : 0 < μ⁻¹ := inv_pos.2 hμ
  have hf1 : ∀ ξ : 𝔼, 4 < ‖ξ‖ → 𝓕 (⇑(xbbDil μ⁻¹ hc.ne' f)) ξ = 0 := by
    intro ξ hξ
    refine xbb_fourier_dil_zero' hc f hf ξ ?_
    have e : μ⁻¹ * (4 * μ) = 4 := by field_simp
    rw [e]; exact hξ
  have hΓ1 : ∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑(xbbDil μ⁻¹ hc.ne' Γ)) ξ = 0 := by
    intro ξ hξ
    refine xbb_fourier_dil_zero hc Γ hΓ ξ ?_
    have e : μ⁻¹ * μ = 1 := by field_simp
    rw [e]; exact hξ
  have hfB1 : ∀ x, ‖(xbbDil μ⁻¹ hc.ne' f) x‖ ≤ B := fun x => hfB _
  have h1 := h _ _ hf1 hΓ1 B hB hfB1
  have e : (fun x => (xbbDil μ⁻¹ hc.ne' f) x * (xbbDil μ⁻¹ hc.ne' Γ) x) =
      ⇑(xbbDil μ⁻¹ hc.ne' (prodS f Γ)) := rfl
  rw [e, xbbN_dil β hc, xbbN_dil β hc] at h1
  have hs0 : ENNReal.ofReal (μ⁻¹ ^ (β - (d : ℝ) / 2)) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine xbb_cancel hs0 ENNReal.ofReal_ne_top ?_
  calc ENNReal.ofReal (μ⁻¹ ^ (β - (d : ℝ) / 2)) * xbbN β (fun x => f x * Γ x)
      = ENNReal.ofReal (μ⁻¹ ^ (β - (d : ℝ) / 2)) * xbbN β ⇑(prodS f Γ) := rfl
    _ ≤ C * ENNReal.ofReal B * (ENNReal.ofReal (μ⁻¹ ^ (β - (d : ℝ) / 2)) * xbbN β ⇑Γ) := h1
    _ = _ := by ring


lemma xbb_fourier_smul (a : ℂ) (G : 𝓢(𝔼, ℂ)) (ξ : 𝔼) : 𝓕 (⇑(a • G)) ξ = a * 𝓕 (⇑G) ξ := by
  have h : (𝓕 (a • G) : 𝓢(𝔼, ℂ)) = a • 𝓕 G := by
    have := (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := 𝔼)).map_smul a G
    simpa only [SchwartzMap.fourierTransformCLM_apply] using this
  rw [← SchwartzMap.fourier_coe, h, SchwartzMap.smul_apply, SchwartzMap.fourier_coe, smul_eq_mul]

lemma xbb_comp_dil {β c : ℝ} (hc : 0 < c) {f G : 𝓢(𝔼, ℂ)} (hG : XComp β f G) :
    XComp β (xbbDil c hc.ne' f) (((c ^ β : ℝ) : ℂ) • xbbDil c hc.ne' G) := by
  intro ξ
  rw [xbb_fourier_smul, xbb_fourier_dil hc, xbb_fourier_dil hc, hG]
  have hn : ‖c⁻¹ • ξ‖ = c⁻¹ * ‖ξ‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le]
  have e : (2 * Real.pi * ‖c⁻¹ • ξ‖) ^ β = (c ^ β)⁻¹ * (2 * Real.pi * ‖ξ‖) ^ β := by
    rw [hn, ← Real.inv_rpow hc.le, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; ring
  rw [e]
  simp only [Complex.real_smul]
  push_cast
  have hcb : ((c ^ β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hc β).ne'
  field_simp


lemma xbbQ0_toReal {β : ℝ} (hβ : 0 < β) : (xbbQ0 d β).toReal = d / β := by
  unfold xbbQ0
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma xbbQ1_toReal {β : ℝ} (hβd : 2 * β < d) : (xbbQ1 d β).toReal = 2 * d / (d - 2 * β) := by
  have hden : 0 < (d : ℝ) - 2 * β := by linarith
  unfold xbbQ1
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma xbbQ0_ne_zero {β : ℝ} (hβ : 0 < β) (hd : 1 ≤ d) : xbbQ0 d β ≠ 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold xbbQ0
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

lemma xbbQ0_ne_top (d : ℕ) (β : ℝ) : xbbQ0 d β ≠ ⊤ := ENNReal.ofReal_ne_top
lemma xbbQ1_ne_top (d : ℕ) (β : ℝ) : xbbQ1 d β ≠ ⊤ := ENNReal.ofReal_ne_top

lemma xbbQ1_ne_zero {β : ℝ} (hβd : 2 * β < d) (hd : 1 ≤ d) : xbbQ1 d β ≠ 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * β := by linarith
  unfold xbbQ1
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

/-- the Kato–Ponce estimate for a Fourier-high factor, at scale `μ` -/
lemma xbb_pair_high_scaled (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (μ : ℝ), 0 < μ → ∀ (f G Γ : 𝓢(𝔼, ℂ)), XComp β f G →
      (∀ ξ : 𝔼, ‖ξ‖ < 2 * μ → 𝓕 (⇑f) ξ = 0) → (∀ ξ : 𝔼, ‖ξ‖ < μ → 𝓕 (⇑Γ) ξ = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) →
        xbbN β (fun x => f x * Γ x) ≤ C * (eLpNorm (⇑G) (xbbQ0 d β) volume *
          eLpNorm (⇑Γ) (xbbQ1 d β) volume + ENNReal.ofReal B * xbbN β ⇑Γ) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨C, hC, h⟩ := xbb_pair_high hd hβ hβd
  refine ⟨C, hC, fun μ hμ f G Γ hG hf hΓ B hB hfB => ?_⟩
  set c : ℝ := μ⁻¹ with hcdef
  have hc : 0 < c := inv_pos.2 hμ
  have hf1 : ∀ ξ : 𝔼, ‖ξ‖ < 2 → 𝓕 (⇑(xbbDil c hc.ne' f)) ξ = 0 := by
    intro ξ hξ
    refine xbb_fourier_dil_zero hc f hf ξ ?_
    have e : c * (2 * μ) = 2 := by rw [hcdef]; field_simp
    rw [e]; exact hξ
  have hΓ1 : ∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑(xbbDil c hc.ne' Γ)) ξ = 0 := by
    intro ξ hξ
    refine xbb_fourier_dil_zero hc Γ hΓ ξ ?_
    have e : c * μ = 1 := by rw [hcdef]; field_simp
    rw [e]; exact hξ
  have hfB1 : ∀ x, ‖(xbbDil c hc.ne' f) x‖ ≤ B := fun x => hfB _
  have h1 := h _ _ _ (xbb_comp_dil hc hG) hf1 hΓ1 B hB hfB1
  have e : (fun x => (xbbDil c hc.ne' f) x * (xbbDil c hc.ne' Γ) x) =
      ⇑(xbbDil c hc.ne' (prodS f Γ)) := rfl
  rw [e, xbbN_dil β hc, xbbN_dil β hc] at h1
  have hq0 : (xbbQ0 d β) ≠ 0 := xbbQ0_ne_zero hβ hd1
  have hq1 : (xbbQ1 d β) ≠ 0 := xbbQ1_ne_zero hβd hd1
  have hcoe : ⇑((((c ^ β : ℝ) : ℂ)) • xbbDil c hc.ne' G) =
      (((c ^ β : ℝ) : ℂ)) • ⇑(xbbDil c hc.ne' G) := rfl
  rw [hcoe, eLpNorm_const_smul, xbb_eLpNorm_dil hc _ hq0 (xbbQ0_ne_top d β),
    xbb_eLpNorm_dil hc _ hq1 (xbbQ1_ne_top d β), xbbQ0_toReal hβ, xbbQ1_toReal hβd] at h1
  set s := ENNReal.ofReal (c ^ (β - (d : ℝ) / 2)) with hs
  have hs0 : s ≠ 0 := by
    simp only [hs, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hnorm : ‖(((c ^ β : ℝ) : ℂ))‖ₑ = ENNReal.ofReal (c ^ β) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hnorm] at h1
  have hprod : ENNReal.ofReal (c ^ β) * ENNReal.ofReal (c ^ (-(d : ℝ) / (d / β))) *
      ENNReal.ofReal (c ^ (-(d : ℝ) / (2 * d / (d - 2 * β)))) = s := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hs,
      ← Real.rpow_add hc, ← Real.rpow_add hc]
    congr 2
    have hden : (d : ℝ) - 2 * β ≠ 0 := by linarith
    field_simp
    ring
  refine xbb_cancel hs0 ENNReal.ofReal_ne_top ?_
  calc s * xbbN β (fun x => f x * Γ x) = s * xbbN β ⇑(prodS f Γ) := rfl
    _ ≤ C * (ENNReal.ofReal (c ^ β) * (ENNReal.ofReal (c ^ (-(d : ℝ) / (d / β))) *
          eLpNorm (⇑G) (xbbQ0 d β) volume) *
          (ENNReal.ofReal (c ^ (-(d : ℝ) / (2 * d / (d - 2 * β)))) * eLpNorm (⇑Γ) (xbbQ1 d β) volume) +
          ENNReal.ofReal B * (s * xbbN β ⇑Γ)) := h1
    _ = s * (C * (eLpNorm (⇑G) (xbbQ0 d β) volume * eLpNorm (⇑Γ) (xbbQ1 d β) volume +
          ENNReal.ofReal B * xbbN β ⇑Γ)) := by
        rw [← hprod]; ring

end HRS.Commutator.Whole.XBB
