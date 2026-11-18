import HRS.Commutator.Torus.TSAMPAux1

/-!
# T-SAMP helpers, part 2: scaling of the cut-off kernel `ψ_L`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_chi_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun ξ : Euc d => (((Whole.chi (c • ξ)) : ℝ) : ℂ)) := by
  have hcont : Continuous (fun ξ : Euc d => (((Whole.chi (c • ξ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((Whole.cmxFB_chi_contDiff (d := d)).continuous.comp (continuous_const_smul c))
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 / c)) ?_)
  intro ξ hξ
  rw [mem_closedBall_zero_iff, not_le] at hξ
  have h2 : 2 ≤ ‖c • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_lt_iff₀ hc] at hξ
    nlinarith
  simp [Whole.cmxFB_chi_zero h2]

lemma tsamp_fourier_inj {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hFT : ∀ ξ, 𝓕 (fun x : Euc d => ((f x : ℝ) : ℂ)) ξ = 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) ξ)
    (hI : Integrable (𝓕 (fun x : Euc d => ((f x : ℝ) : ℂ)))) : f = g := by
  have hFg : 𝓕 (fun x : Euc d => ((f x : ℝ) : ℂ)) = 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
    funext hFT
  have h1 : 𝓕⁻ (𝓕 (fun x : Euc d => ((f x : ℝ) : ℂ))) = fun x : Euc d => ((f x : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hf).fourierInv_fourier_eq hfi.ofReal hI
  have h2 : 𝓕⁻ (𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ))) = fun x : Euc d => ((g x : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp hg).fourierInv_fourier_eq hgi.ofReal (hFg ▸ hI)
  rw [hFg] at h1
  have h3 : (fun x : Euc d => ((f x : ℝ) : ℂ)) = fun x => ((g x : ℝ) : ℂ) := by
    refine h1.symm.trans ?_
    exact h2
  funext x
  exact_mod_cast congrFun h3 x

lemma tsamp_psi_scale {η : ℝ} (hη : 0 < η) :
    (Whole.psiL (d := d) η⁻¹ : Euc d → ℝ) = textKeta (Whole.psiL (d := d) 1) 0 η := by
  obtain ⟨hc1, hi1, -, -, hft1⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
  obtain ⟨hc2, hi2, -, -, hft2⟩ := text_psiL_props (d := d) 1 one_pos
  refine tsamp_fourier_inj hc1 ?_ hi1 (text_Keta_integrable hi2 hη 0) ?_ ?_
  · unfold textKeta
    exact continuous_const.mul (hc2.comp (continuous_const_smul _))
  · intro ξ
    rw [text_fourier_Keta hη _ 0 ξ, hft1, hft2]
    simp [smul_smul, inv_inv]
  · have : (fun ξ : Euc d => 𝓕 (fun x : Euc d => ((Whole.psiL (d := d) η⁻¹ x : ℝ) : ℂ)) ξ) =
        fun ξ => (((Whole.chi ((η⁻¹)⁻¹ • ξ)) : ℝ) : ℂ) := funext hft1
    have h2 : 𝓕 (fun x : Euc d => ((Whole.psiL (d := d) η⁻¹ x : ℝ) : ℂ)) =
        fun ξ => (((Whole.chi ((η⁻¹)⁻¹ • ξ)) : ℝ) : ℂ) := this
    rw [h2]
    exact tsamp_chi_integrable _ (by positivity)

end HRS.Commutator.TorusNote
