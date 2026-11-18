import HRS.Commutator.Whole.Local
import HRS.Commutator.Whole.INHOMAux3

/-!
# CMX-INHOM auxiliary 4: the Fourier transform of `∇g_{>1}`

`inhom_ghi_ae`: componentwise, `(∇g_{>1})_i = c K_i` a.e. with `K_i ∈ L¹` and `𝓕 K_i = (1-χ) ξ_i |ξ|^{-(d-s)}`
(a copy of `cmxMY_ghi_ae` retaining the Fourier transform of `K`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_ghi_ae (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℂ, ∀ i : Fin d, ∃ K : Euc d → ℂ, Integrable K ∧
      (∀ ξ : Euc d, 𝓕 K ξ = ((1 - chi ξ : ℝ) : ℂ) * cmxMY_hi d s i ξ) ∧
      ∀ᵐ x : Euc d, ((ghiForce s x i : ℝ) : ℂ) = c * K x := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c, hc⟩ := cmxMY_kernGrad_fourier hd hs0 hsd (s := s)
  refine ⟨c, fun i => ?_⟩
  have hγ : 0 < ((d : ℝ) - s) - 1 := by linarith
  obtain ⟨K, hK, hF, hfar, -⟩ := cmxMY_LP_homog hd1 hγ (cmxMY_hi d s i)
    (fun η hη => cmxMY_hi_smooth s i η hη) (fun t η ht => cmxMY_hi_hom s i t η ht)
  refine ⟨K, hK, fun ξ => ?_, ?_⟩
  · rw [hF ξ, Complex.real_smul]
  have hKer := cmxFB_kerOK hd hs0 hsd
  have hloc1 : LocallyIntegrable (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) := by
    have h1 := cmxMY_locInt_comp _ hKer i
    have h2 : LocallyIntegrable (fun x : Euc d => ((gloForce s x i : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
        (cmxMY_gloForce_continuous hd hs0 hsd))).locallyIntegrable
    have e : (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) =
        (fun x : Euc d => ((kernGrad s x i : ℝ) : ℂ)) - fun x : Euc d => ((gloForce s x i : ℝ) : ℂ) := by
      funext x
      simp only [ghiForce, PiLp.sub_apply, Pi.sub_apply]
      push_cast; ring
    rw [e]
    exact h1.sub h2
  have hloc2 : LocallyIntegrable (fun x : Euc d => c * K x) := (hK.const_mul c).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 (fun g hg hgc => ?_)
  have hgc' : HasCompactSupport (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
    hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hgs' : ContDiff ℝ ∞ (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  set S : SchwartzMap (Euc d) ℂ := hgc'.toSchwartzMap hgs' with hS
  have hSg : ∀ x, S x = ((g x : ℝ) : ℂ) := fun x => rfl
  set Φ : SchwartzMap (Euc d) ℂ := 𝓕⁻ S with hΦ
  have hΦS : ∀ x, 𝓕 (⇑Φ) x = ((g x : ℝ) : ℂ) := by
    intro x
    have h : (𝓕 Φ : SchwartzMap (Euc d) ℂ) = S := FourierTransform.fourier_fourierInv_eq S
    have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T x) h
    rw [← hSg x, ← h2]
    rfl
  set Φ' : SchwartzMap (Euc d) ℂ := Φ - cmxMY_chiPhi Φ with hΦ'
  have hΦ'0 : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → Φ' ξ = 0 := by
    intro ξ hξ
    show Φ ξ - ((chi ξ : ℝ) : ℂ) * Φ ξ = 0
    rw [cmxFB_chi_one hξ]; simp
  have hL : ∫ x : Euc d, g x • ((ghiForce s x i : ℝ) : ℂ) =
      c * ∫ ξ : Euc d, cmxMY_hi d s i ξ * Φ' ξ := by
    have e1 : ∀ x : Euc d, g x • ((ghiForce s x i : ℝ) : ℂ) =
        ((ghiForce s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x := by
      intro x; rw [hΦS, Complex.real_smul]; ring
    simp_rw [e1]
    rw [cmxMY_ghi_pairing hd hs0 hsd i Φ]
    exact hc i Φ' hΦ'0
  have hR : ∫ x : Euc d, g x • (c * K x) =
      c * ∫ ξ : Euc d, cmxMY_hi d s i ξ * Φ' ξ := by
    have e1 : ∀ x : Euc d, g x • (c * K x) = c * (K x * 𝓕 (⇑Φ) x) := by
      intro x; rw [hΦS, Complex.real_smul]; ring
    simp_rw [e1]
    rw [integral_const_mul, integral_mul_fourier_eq K Φ hK Φ.integrable]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hF ξ]
    show _ = cmxMY_hi d s i ξ * (Φ ξ - ((chi ξ : ℝ) : ℂ) * Φ ξ)
    rw [Complex.real_smul]
    push_cast; ring
  rw [hL, hR]

end HRS.Commutator.Whole
