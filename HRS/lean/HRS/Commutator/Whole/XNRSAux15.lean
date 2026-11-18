import HRS.Commutator.Whole.XNRSAux14
import HRS.Commutator.Whole.LocalAuxSAMP2Fourier
import HRS.Commutator.Whole.LocalAuxFC2

/-!
# Packet X-NRS, part 15: the force `∇g * φ` as a derivative of `h = Λ^{-(d-s)} φ`

For `φ` Schwartz with Fourier support where `ρ = 1`, `h = Λ^{-(d-s)} φ`:
`∫ ∇g_i(x-y) φ(y) dy = c' ∂_i h(x)` with a constant `c'` depending only on `d, s`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xfourier_fourier (f : 𝓢(Euc d, ℂ)) (z : Euc d) : 𝓕 (𝓕 f : 𝓢(Euc d, ℂ)) z = f (-z) := by
  have h0 : 𝓕⁻ (𝓕 f : 𝓢(Euc d, ℂ)) = f := FourierTransform.fourierInv_fourier_eq f
  have h := congrArg (fun F : 𝓢(Euc d, ℂ) => F (-z)) h0
  rw [xfourierInv_apply] at h
  simpa using h

lemma xfourier_transl_neg (φ : 𝓢(Euc d, ℂ)) (x z : Euc d) :
    𝓕 (𝓕 (HRS.PDE.ToolboxRd.FourierAux.translSchwartz (-x) φ) : 𝓢(Euc d, ℂ)) z = φ (x - z) := by
  rw [xfourier_fourier, HRS.PDE.ToolboxRd.FourierAux.translSchwartz_apply]
  congr 1; abel

theorem xK0_conv (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c' : ℂ, ∀ (ρ : Euc d → ℝ) (_hρ : XGoodCut ρ) (φ : 𝓢(Euc d, ℂ)) (_hφ : XInD ρ φ)
      (i : Fin d) (x : Euc d),
      ∫ y, ((kernGrad s (x - y) i : ℝ) : ℂ) * φ y =
        c' * xdr i (xlam (-((d : ℝ) - s)) ρ φ) x := by
  obtain ⟨c, hc⟩ := HRS.Commutator.Whole.SAMP2.kernGrad_fourier_full hd hs0 hsd
  refine ⟨c * ((2 * Real.pi) ^ ((d : ℝ) - s) : ℝ) / (2 * Real.pi * Complex.I), fun ρ hρ φ hφ i x => ?_⟩
  set h := xlam (-((d : ℝ) - s)) ρ φ with hh
  have ha : ∫ y, ((kernGrad s (x - y) i : ℝ) : ℂ) * φ y =
      ∫ z, ((kernGrad s z i : ℝ) : ℂ) * φ (x - z) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun z => ((kernGrad s z i : ℝ) : ℂ) * φ (x - z)) x
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel]
  set Φ : 𝓢(Euc d, ℂ) := 𝓕 (HRS.PDE.ToolboxRd.FourierAux.translSchwartz (-x) φ) with hΦ
  have hb : ∀ z, φ (x - z) = 𝓕 Φ z := fun z => (xfourier_transl_neg φ x z).symm
  have hc1 := hc i Φ
  have hΦξ : ∀ ξ : Euc d, Φ ξ = Complex.exp (((2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * 𝓕 φ ξ := by
    intro ξ
    rw [hΦ, HRS.PDE.ToolboxRd.FourierAux.fourier_translSchwartz]
    unfold HRS.PDE.ToolboxRd.FourierAux.phase
    congr 2
    rw [inner_neg_left]; push_cast; ring
  rw [ha]
  have hb' : ∫ z, ((kernGrad s z i : ℝ) : ℂ) * φ (x - z) =
      ∫ z, ((kernGrad s z i : ℝ) : ℂ) * 𝓕 (⇑Φ) z :=
    integral_congr_ae (Eventually.of_forall fun z => by show _ * φ (x - z) = _ * (𝓕 Φ) z; rw [hb z])
  rw [hb', hc1]
  -- the derivative side
  have hinv : xdr i h x = ∫ ξ, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
      𝓕 (xdr i h) ξ := by
    have h0 : 𝓕⁻ (𝓕 (xdr i h) : 𝓢(Euc d, ℂ)) = xdr i h := FourierTransform.fourierInv_fourier_eq _
    have h1 := congrArg (fun F : 𝓢(Euc d, ℂ) => F x) h0
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe, Real.fourierInv_eq'] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    rfl
  rw [hinv]
  rw [mul_div_assoc, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have hx : 𝓕 (xdr i h) ξ = (2 * Real.pi * Complex.I * (ξ i : ℂ)) *
      ((((2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) : ℝ)) : ℂ) * 𝓕 φ ξ := by
    rw [fourier_xdr, hh, fourier_xlam_of_inD hρ hφ]; ring
  rw [hx, hΦξ, real_inner_comm]
  have hpow : (((2 * Real.pi * ‖ξ‖) ^ (-((d : ℝ) - s)) : ℝ) : ℂ) =
      (((2 * Real.pi) ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * (((‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ)) : ℂ) := by
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)]; push_cast; ring
  have hAB : ((((2 * Real.pi) ^ ((d : ℝ) - s) : ℝ)) : ℂ) *
      (((2 * Real.pi) ^ (-((d : ℝ) - s)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]; simp
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hpow]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have key : (((2 * Real.pi) ^ ((d : ℝ) - s) : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) *
      (Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        (2 * (Real.pi : ℂ) * Complex.I * (ξ i : ℂ) *
          ((((2 * Real.pi) ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * (((‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ)) : ℂ)) * 𝓕 φ ξ)) =
      ((((2 * Real.pi) ^ ((d : ℝ) - s) : ℝ) : ℂ) * (((2 * Real.pi) ^ (-((d : ℝ) - s)) : ℝ) : ℂ)) *
        (Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * (ξ i : ℂ) *
          (((‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ)) : ℂ) * 𝓕 φ ξ) := by
    field_simp
  rw [key, hAB, one_mul]
  push_cast
  ring

end HRS.Commutator.Whole.XNRS
