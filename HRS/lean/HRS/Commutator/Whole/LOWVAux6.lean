import HRS.Commutator.Whole.LOWVAux5

/-!
# CMX-LOWV auxiliary 6: the low-frequency part `a = ψ_Λ * σ` of an admissible measure is a real Schwartz function
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

theorem lowv_psi_meas {Λ : ℝ} (hΛ0 : 0 < Λ) (μ : Measure (Euc d)) [IsFiniteMeasure μ] (x : Euc d) :
    ((∫ z, psiL Λ (x - z) ∂μ : ℝ) : ℂ) =
      ∫ ξ, cmxFB_gL d Λ ξ * Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        fm μ ξ := by
  have hint : Integrable (cmxFB_gL d Λ) := (cmxFB_G (d := d) Λ hΛ0).integrable
  rw [← integral_complex_ofReal]
  have := finv_integral_meas μ (cmxFB_gL d Λ) hint x
  simp_rw [cmxFB_finv_eq] at this
  rw [this]
  rfl

theorem lowv_a_exists {Λ : ℝ} (hΛ0 : 0 < Λ) (σ : SMeas d) (h : IsAdmissible σ) :
    ∃ φ : SchwartzMap (Euc d) ℂ,
      (∀ x, φ x = ((σ.int (fun z => psiL Λ (x - z)) : ℝ) : ℂ)) ∧
      ∀ ξ, 𝓕 (⇑φ) ξ = cmxFB_gL d Λ ξ * σ.fourier ξ := by
  obtain ⟨hp, hn⟩ := h.1
  haveI := hp
  haveI := hn
  have hcd : ContDiff ℝ ∞ (fun ξ : Euc d => cmxFB_gL d Λ ξ * σ.fourier ξ) :=
    (cmxFB_gL_contDiff Λ).mul (contDiff_sfourier σ h)
  have hcs : HasCompactSupport (fun ξ : Euc d => cmxFB_gL d Λ ξ * σ.fourier ξ) :=
    (cmxFB_gL_compact hΛ0).mul_right
  set Gs : SchwartzMap (Euc d) ℂ := hcs.toSchwartzMap hcd with hGs
  have hGsx : ∀ ξ, Gs ξ = cmxFB_gL d Λ ξ * σ.fourier ξ := fun ξ => rfl
  refine ⟨𝓕⁻ Gs, fun x => ?_, fun ξ => ?_⟩
  · rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    unfold SMeas.int
    rw [Complex.ofReal_sub, lowv_psi_meas hΛ0 σ.pos x, lowv_psi_meas hΛ0 σ.neg x]
    have hM : Integrable (cmxFB_gL d Λ) := (cmxFB_G (d := d) Λ hΛ0).integrable
    rw [← integral_sub (finv_meas_integrable _ _ hM x) (finv_meas_integrable _ _ hM x)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, hGsx, SMeas.fourier, fm]
    ring
  · have : 𝓕 (𝓕⁻ Gs) = Gs := FourierTransform.fourier_fourierInv_eq _
    rw [← SchwartzMap.fourier_coe, this, hGsx]

end HRS.Commutator.Whole
