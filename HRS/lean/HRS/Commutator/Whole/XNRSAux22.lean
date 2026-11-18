import HRS.Commutator.Whole.XNRSAux21

/-!
# Packet X-NRS, part 22: scaling of the cutoff kernels
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xKr_scale (ψ : Euc d → ℝ) {R : ℝ} (hR : 0 < R) (z : Euc d) :
    xKr (fun ξ => ψ (R⁻¹ • ξ)) z = R ^ d * xKr ψ (R • z) := by
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun ξ : Euc d => Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ (R⁻¹ • ξ)) R
  have e1 : ∀ η : Euc d, Real.cos (2 * Real.pi * inner ℝ z (R • η)) * ψ (R⁻¹ • R • η) =
      Real.cos (2 * Real.pi * inner ℝ (R • z) η) * ψ η := by
    intro η
    rw [inv_smul_smul₀ hR.ne', real_inner_smul_right, real_inner_smul_left]
  simp only [e1] at h
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  rw [hfr, abs_of_pos (by positivity), smul_eq_mul] at h
  unfold xKr
  have hRd : (R ^ d : ℝ) ≠ 0 := by positivity
  change ∫ ξ, Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ (R⁻¹ • ξ) = _
  rw [show (∫ ξ : Euc d, Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ (R⁻¹ • ξ)) =
    R ^ d * ((R ^ d)⁻¹ * ∫ ξ : Euc d, Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ (R⁻¹ • ξ)) by
      field_simp, ← h]

/-- `Φ = ∫ cos(2π⟨z,ξ⟩) χ(ξ) dξ`. -/
def xΦ (z : Euc d) : ℝ := xKr xchi z

/-- `Φ` as a Schwartz function. -/
def xΦS (d : ℕ) : 𝓢(Euc d, ℂ) := 𝓕⁻ (xsch (xchi : Euc d → ℝ) xchi_smooth xchi_cpt)

lemma xΦS_apply (z : Euc d) : xΦS d z = ((xΦ z : ℝ) : ℂ) :=
  xinvF_even _ xchi (fun ξ => rfl) xchi_neg z

lemma xΦ_integral : ∫ z : Euc d, xΦ z = 1 := by
  have h1 : (𝓕 (xΦS d : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ)) 0 =
      xsch (xchi : Euc d → ℝ) xchi_smooth xchi_cpt 0 := by
    unfold xΦS
    rw [FourierTransform.fourier_fourierInv_eq]
  have h2 : (𝓕 (xΦS d : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ)) 0 = ∫ z : Euc d, ((xΦ z : ℝ) : ℂ) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [xΦS_apply]
  rw [h2, integral_complex_ofReal, xsch_apply] at h1
  have h0 : xchi (0 : Euc d) = 1 := xchi_one (by simp)
  rw [h0] at h1
  exact_mod_cast h1

lemma xKr_sub {ψ₁ ψ₂ : Euc d → ℝ} (h₁ : Continuous ψ₁) (c₁ : HasCompactSupport ψ₁)
    (h₂ : Continuous ψ₂) (c₂ : HasCompactSupport ψ₂) (z : Euc d) :
    xKr (fun ξ => ψ₁ ξ - ψ₂ ξ) z = xKr ψ₁ z - xKr ψ₂ z := by
  unfold xKr
  have hc : Continuous (fun ξ : Euc d => Real.cos (2 * Real.pi * inner ℝ z ξ)) :=
    Real.continuous_cos.comp (continuous_const.mul (continuous_const.inner continuous_id))
  have i1 : Integrable (fun ξ : Euc d => Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ₁ ξ) :=
    (hc.mul h₁).integrable_of_hasCompactSupport c₁.mul_left
  have i2 : Integrable (fun ξ : Euc d => Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ₂ ξ) :=
    (hc.mul h₂).integrable_of_hasCompactSupport c₂.mul_left
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only; ring

lemma xσ_eq_sub {n : ℝ} (hn : 2 ≤ n) (ξ : Euc d) :
    xσ n ξ = xchi (n⁻¹ • ξ) - xchi (n • ξ) := by
  unfold xσ xcut
  by_cases h : xchi (n • ξ) = 0
  · rw [h]; ring
  · have : ‖n • ξ‖ < 2 := by
      by_contra hc
      push Not at hc
      exact h (xchi_zero hc)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    have h1 : xchi (n⁻¹ • ξ) = 1 := by
      apply xchi_one
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [inv_mul_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg ξ]
    rw [h1]; ring

lemma xKr_xσ {n : ℝ} (hn : 2 ≤ n) (z : Euc d) :
    xKr (xσ n) z = n ^ d * xΦ (n • z) - (n⁻¹) ^ d * xΦ (n⁻¹ • z) := by
  have hn0 : 0 < n := by linarith
  have hfun : (xσ n : Euc d → ℝ) = fun ξ => xchi (n⁻¹ • ξ) - xchi (n • ξ) :=
    funext (xσ_eq_sub hn)
  have hc1 : Continuous (fun ξ : Euc d => xchi (n⁻¹ • ξ)) :=
    xchi_smooth.continuous.comp (continuous_const_smul _)
  have hc2 : Continuous (fun ξ : Euc d => xchi (n • ξ)) :=
    xchi_smooth.continuous.comp (continuous_const_smul _)
  have hs1 : HasCompactSupport (fun ξ : Euc d => xchi (n⁻¹ • ξ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * n)) fun ξ hξ => ?_
    apply xchi_zero
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn0]
    have : 2 * n < ‖ξ‖ := by simpa using hξ
    rw [le_inv_mul_iff₀ hn0]; linarith
  have hs2 : HasCompactSupport (fun ξ : Euc d => xchi (n • ξ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * n⁻¹)) fun ξ hξ => ?_
    apply xchi_zero
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hn0]
    have : 2 * n⁻¹ < ‖ξ‖ := by simpa using hξ
    have h3 : 2 < n * ‖ξ‖ := by
      calc 2 = n * (2 * n⁻¹) := by field_simp
        _ < n * ‖ξ‖ := by gcongr
    linarith
  rw [hfun, xKr_sub hc1 hs1 hc2 hs2]
  have e1 := xKr_scale xchi hn0 z
  have e2 := xKr_scale xchi (inv_pos.2 hn0) z
  rw [inv_inv] at e2
  rw [e1, e2]
  rfl

end HRS.Commutator.Whole.XNRS
