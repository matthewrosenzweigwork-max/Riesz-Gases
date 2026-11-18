import HRS.Commutator.Whole.INHOMAux12
import HRS.Commutator.Whole.External

/-!
# CMX-INHOM auxiliary 13: the `NRS` and the `low_velocity` terms for the high-frequency part `a₁`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_subTransport_nonneg {v : Euc d → Euc d} {K : ℝ} (hv : SubTransport d s v K) : 0 ≤ K := by
  obtain ⟨L, F, hF0, -, -, hK⟩ := hv
  have : (0 : ℝ) ≤ L := L.coe_nonneg
  linarith

/-- `Lemma 4.1` (`low_velocity`), re-derived from its auxiliary lemmas (the theorem itself lives in
`Continuous.lean`, which imports this file). -/
theorem inhom_low_velocity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ σ : SMeas d, IsAdmissible σ → (s = 0 → σ.mass = 0) →
        ENNReal.ofReal |Ccomm (gloForce s) (Pleq 1 v) σ| ≤
          ENNReal.ofReal (C * K) * homSqE (-alphaE d s) (lowFreq 4 σ.fourier) := by
  obtain ⟨C, hC, hmain⟩ := lowv_perLam hd hs0 hsd
  refine ⟨C, hC, fun v K hv σ hσ hmass => ?_⟩
  have ht : -alphaE d s ≤ 0 := by
    unfold alphaE
    linarith
  exact lowv_limit (by omega) (-alphaE d s) ht σ hσ _ (C * K)
    (fun Λ h4 h5 => hmain v K hv σ hσ hmass Λ h4 h5)

lemma inhom_gL_zero : cmxFB_gL d (1 / 16) (0 : Euc d) = 1 := by
  unfold cmxFB_gL
  simp [cmxFB_chi_one (d := d) (ξ := 0) (by simp)]

lemma inhom_mass_zero {b : Euc d → ℝ} {φ ψ : SchwartzMap (Euc d) ℂ}
    (hψ : ∀ x, ψ x = ((b x : ℝ) : ℂ))
    (hF : ∀ ξ, 𝓕 (⇑ψ) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) : ∫ x, b x = 0 := by
  have h1 : 𝓕 (⇑ψ) 0 = ∫ x, ψ x := by
    rw [Real.fourier_eq]; simp
  have h2 : 𝓕 (⇑ψ) 0 = 0 := by rw [hF, inhom_gL_zero]; simp
  have h3 : ((∫ x, b x : ℝ) : ℂ) = 0 := by
    rw [← integral_complex_ofReal, ← h2, h1]
    exact integral_congr_ae (Eventually.of_forall fun x => (hψ x).symm)
  exact_mod_cast h3

/-- the `NRS` term: `|𝒞_g(v,b)| ≲ K ‖a‖²_{H^{-α}}` for `b` the high-frequency part. -/
theorem inhom_T_nrs (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ ψ : SchwartzMap (Euc d) ℂ) (b : Euc d → ℝ), (∀ x, ψ x = ((b x : ℝ) : ℂ)) →
        (∀ ξ, 𝓕 (⇑ψ) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) →
        ENNReal.ofReal |CcommFun (kernGrad s) v b| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  obtain ⟨Cn, hCn, hnrs⟩ := nrs_commutator hd hs0 hsd
  have hα : 0 < alphaE d s := by
    unfold alphaE; have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨Cn * (1 + 64 / Real.pi ^ 2) ^ alphaE d s, by positivity, fun v K hv φ ψ b hψ hF => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  have hmass : s = 0 → ∫ x, b x = 0 := fun _ => inhom_mass_zero hψ hF
  have h1 := hnrs v K hv b ⟨ψ, hψ⟩ hmass
  have h2 : homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 b) ≤
      ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ alphaE d s) * inhom_Sob (-alphaE d s) φ := by
    rw [inhom_homSqE_eq hψ]
    refine inhom_hom_le hα (fun ξ => 𝓕 (⇑ψ) ξ) (fun ξ => ?_)
    rw [hF ξ, norm_mul]
  refine h1.trans ?_
  calc ENNReal.ofReal (Cn * K) * homSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 b)
      ≤ ENNReal.ofReal (Cn * K) * (ENNReal.ofReal ((1 + 64 / Real.pi ^ 2) ^ alphaE d s) *
          inhom_Sob (-alphaE d s) φ) := by gcongr
    _ = ENNReal.ofReal (Cn * (1 + 64 / Real.pi ^ 2) ^ alphaE d s * K) * inhom_Sob (-alphaE d s) φ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

end HRS.Commutator.Whole
