import HRS.MS.S111K4Q5
import HRS.MS.S21E_Uniq
import HRS.MS.S111X1Aux5
import HRS.MS.S111X2Aux21

/-!
# S11.1 / V02 (S11K4), packet `R26-T6C.V07` (part): identification of the stationary cross-covariance density on the early history

For `0 < r ≤ t` the density `χ^r` of `ψ ↦ Cov(Z^r(ψ), Z^t(φ))` of the stationary linear evolution is `ρ · h`, `h` the response of
`U^{r,t} φ` (here with the stationary preparation `γ = β`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

theorem k4_cross_density_ident (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) {h : Euc d → ℝ}
    (hresp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) h)
    (hhm : MemLp h 2 (HRS.Whole.withDensityReal ρ)) {χ : Euc d → ℝ}
    (hχi : ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * χ x))
    (hχ : ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) ψ →
      ∫ x, ψ x * χ x = linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ) :
    χ =ᵐ[volume] fun x => ρ x * h x := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨g, hg⟩ := hex t (hr.le.trans hrt) φ hφ
  have hmean : ∫ x, h x ∂μ = 0 := hresp.1.2
  have hpsiL : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → MemLp ψ 2 μ := fun ψ hψ =>
    HRS.MS.S111X1.x1_osc_memLp T.en.K.meas T.en.K.nonneg T.en.K.bdd hψ
  have hhi : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * h x) μ := fun ψ hψ =>
    (hpsiL ψ hψ).integrable_mul hhm
  have hρh : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * (ρ x * h x)) := fun ψ hψ => by
    have := (tc2_integrable_nu T.prob _).1 (hhi ψ hψ)
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only; ring)
  refine HRS.MS.S21E.s21e_chi_ae_eq (wholeSpaceIndex d) hχi hρh (fun ψ hψ => ?_)
  rw [hχ ψ hψ]
  obtain ⟨F', hF'⟩ := hex r hr.le ψ hψ
  have hq := s111x2_quench hd hs0 hs ha hβ (γ := β) hρ hr hrt hF' hg
  rw [hq, add_sub_cancel_right]
  -- the susceptibility form against the response
  have hpL : MemLp (propagatorW C r t φ) 2 μ := by
    have hpr : propagatorW C r t φ = g r := s111x2_prop_eq hd hs0 hs ha hβ hρ (hr.le.trans hrt) hg ⟨hr.le, hrt⟩
    rw [hpr]
    obtain ⟨B0, h0⟩ := hg.bdd 0 (by norm_num)
    refine MemLp.of_bound (hg.c2 r ⟨hr.le, hrt⟩).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => ?_)
    have := h0 r ⟨hr.le, hrt⟩ x
    simpa [norm_iteratedFDeriv_zero] using this
  have hri : HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) =ᵐ[μ] h := by
    have hex' : ∃ u, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) u := ⟨h, hresp⟩
    have hr' : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ)
        (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ)) := by
      unfold HRS.Whole.responseInverse
      rw [dif_pos hex']
      exact hex'.choose_spec
    exact T.uniq _ _ _ hr' hresp
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  have e1 : ∫ x, HRS.Whole.projMean μ ψ x *
        HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) x ∂μ =
      ∫ x, HRS.Whole.projMean μ ψ x * h x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hri] with x hx
    rw [hx]
  rw [e1]
  have e2 : ∀ x, HRS.Whole.projMean μ ψ x * h x = ψ x * h x - HRS.Whole.pair μ ψ * h x := fun x => by
    simp only [HRS.Whole.projMean]; ring
  simp_rw [e2]
  rw [integral_sub (hhi ψ hψ) ((hhm.integrable (by norm_num)).const_mul _), integral_const_mul, hmean, mul_zero,
    sub_zero, tc2_integral_nu T.prob]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

end HRS.MS.S111K4
