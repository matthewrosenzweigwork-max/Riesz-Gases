import HRS.MS.S111K4Q6
import HRS.MS.S111X2Aux22

/-!
# S11.1 / V02 (S11K4), Pro `R26-T6C.V07` (part): stationarity of the covariance and of the cross-covariance densities
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2

variable {d : ℕ}

theorem k4_susc_symm (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {f h : Euc d → ℝ}
    (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) (hh : MemLp h 2 (HRS.Whole.withDensityReal ρ)) :
    HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β h f := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  exact (s111x2_responseForm hK hβ.le (le_refl β)).symmetry f h hf hh

theorem k4_prop_memLp (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {t r : ℝ} (ht : 0 ≤ t)
    (hr : r ∈ Icc (0 : ℝ) t) {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) :
    MemLp (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) 2
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  obtain ⟨g, hg⟩ := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ t ht φ hφ
  rw [s111x2_prop_eq hd hs0 hs ha hβ hρ ht hg hr]
  obtain ⟨B0, h0⟩ := hg.bdd 0 (by norm_num)
  refine MemLp.of_bound (hg.c2 r hr).continuous.aestronglyMeasurable B0
    (Filter.Eventually.of_forall fun x => ?_)
  have := h0 r hr x
  simpa [norm_iteratedFDeriv_zero] using this

theorem k4_lgc_symm (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t')
    {φ ψ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) (hψ : IsOscTest (wholeSpaceIndex d) ψ) :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) t t' φ ψ =
      linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) t' t ψ φ := by
  unfold linearGaussianCov noiseCovW
  rw [k4_susc_symm hd s a β hs0 hs ha hβ ρ hρ (k4_prop_memLp hd s a β hs0 hs ha hβ ρ hρ ht ⟨le_rfl, ht⟩ hφ)
    (k4_prop_memLp hd s a β hs0 hs ha hβ ρ hρ ht' ⟨le_rfl, ht'⟩ hψ), min_comm t t']
  congr 3
  funext r
  congr 1
  funext x
  rw [real_inner_comm]

theorem k4_lgc_eq (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    {ψ φ : Euc d → ℝ} (hψ : IsOscTest (wholeSpaceIndex d) ψ) (hφ : IsOscTest (wholeSpaceIndex d) φ) :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) := by
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨F', hF'⟩ := hex 0 le_rfl ψ hψ
    have hp : propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 0 ψ = ψ := by
      rw [s111x2_prop_eq hd hs0 hs ha hβ hρ le_rfl hF' ⟨le_rfl, le_rfl⟩]
      exact hF'.terminal
    unfold linearGaussianCov noiseCovW
    rw [hp, min_eq_left hrt]
    simp
  · obtain ⟨F', hF'⟩ := hex r hr ψ hψ
    obtain ⟨g, hg⟩ := hex t (hr.trans hrt) φ hφ
    have hq := s111x2_quench hd hs0 hs ha hβ (γ := β) hρ hpos hrt hF' hg
    rw [hq, add_sub_cancel_right]

/-- Stationarity of the (stationarily prepared) two-time covariance. -/
theorem k4_lgc_shift (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {u : ℝ} (hu : 0 ≤ u) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) {ψ φ : Euc d → ℝ} (hψ : IsOscTest (wholeSpaceIndex d) ψ)
    (hφ : IsOscTest (wholeSpaceIndex d) φ) :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
        (u + r) (u + t) ψ φ =
      linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ := by
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  have key : ∀ (r t : ℝ) (ψ φ : Euc d → ℝ), 0 ≤ r → r ≤ t → IsOscTest (wholeSpaceIndex d) ψ →
      IsOscTest (wholeSpaceIndex d) φ →
      linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
        (u + r) (u + t) ψ φ =
      linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ := by
    intro r t ψ φ hr hrt hψ hφ
    obtain ⟨g, hg⟩ := hex (u + t) (by linarith) φ hφ
    rw [k4_lgc_eq hd s a β hs0 hs ha hβ ρ hρ (by linarith) (by linarith) hψ hφ,
      k4_lgc_eq hd s a β hs0 hs ha hβ ρ hρ hr hrt hψ hφ,
      s111x2_prop_shift hd hs0 hs ha hβ hρ hu hr hrt hg]
  rcases le_total r t with h | h
  · exact key r t ψ φ hr h hψ hφ
  · rw [k4_lgc_symm hd s a β hs0 hs ha hβ ρ hρ (by linarith) (by linarith) hψ hφ,
      k4_lgc_symm hd s a β hs0 hs ha hβ ρ hρ hr ht hψ hφ]
    exact key t r φ ψ ht h hφ hψ

/-- The cross-covariance densities of the windows `u` and `0` agree after the shift. -/
theorem k4_density_shift (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {u : ℝ} (hu : 0 ≤ u) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) {χ χ0 : Euc d → ℝ}
    (hχi : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * χ x))
    (hχ0i : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * χ0 x))
    (hχ : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ →
      ∫ x, ψ x * χ x = linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
        (u + r) (u + t) ψ φ)
    (hχ0 : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ →
      ∫ x, ψ x * χ0 x = linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β)
        r t ψ φ) :
    χ =ᵐ[volume] χ0 :=
  HRS.MS.S21E.s21e_chi_ae_eq (wholeSpaceIndex d) hχi hχ0i fun ψ hψ => by
    rw [hχ ψ hψ, hχ0 ψ hψ, k4_lgc_shift hd s a β hs0 hs ha hβ ρ hρ hu hr ht hψ hφ]

end HRS.MS.S111K4
