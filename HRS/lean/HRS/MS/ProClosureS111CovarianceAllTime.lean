import HRS.MS.S111X1G2
import HRS.MS.S111X2Aux23
import HRS.MS.R26T6D00

/-!
Uniform physical Gaussian covariance in the exact centered L² norm, for all
times and all nonnegative preparation parameters.  The response coercivity at
the bath temperature is chosen before the equilibrium density.  The accepted
fluctuation-dissipation/quench identity and positivity of the actual common
noise supply the estimate.  No Poincare, covariance, or field-moment input is
assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R26T6

variable {d : ℕ}

theorem physical_covariance_all_time (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ L : ℝ, 0 < L ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ t : ℝ, 0 ≤ t → ∀ phi : Euc d → ℝ,
      IsOscTest (wholeSpaceIndex d : ℝ) phi →
      let K := linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
        (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma)
        t t phi phi
      0 ≤ K ∧ K ≤ L * ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) phi x ^ 2
        ∂HRS.Whole.withDensityReal rho := by
  obtain ⟨eta, heta, heta1, hresponse⟩ :=
    s111x2_thermal_response_forms hd s a beta beta hs0 hs ha hbeta hbeta.le
  refine ⟨eta⁻¹, inv_pos.2 heta, fun rho hrho gamma hgamma t ht phi hphi => ?_⟩
  let C := r26t6_thermalCoeff d s a beta rho
  let mu := HRS.Whole.withDensityReal rho
  let f : ℝ → Euc d → ℝ := fun r => propagatorW C r t phi
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hf : IsClassicalAdjointW C t phi f :=
    x1_prop_classical (exist_of_thermal hd hs0 hs ha hbeta hrho t ht phi hphi)
  have hf0 : MemLp (f 0) 2 mu := x1_classical_memLp hf ⟨le_rfl, ht⟩ mu
  have hphim : MemLp phi 2 mu := by
    have h := x1_classical_memLp hf ⟨ht, le_rfl⟩ mu
    rwa [hf.terminal] at h
  have hRFbeta := hresponse rho hrho beta ⟨hbeta.le, le_rfl⟩
  obtain ⟨etag, hetag, hetag1, hresponseg⟩ :=
    s111x2_thermal_response_forms hd s a beta gamma hs0 hs ha hbeta hgamma
  have hRFgamma := hresponseg rho hrho gamma ⟨hgamma, le_rfl⟩
  let V : ℝ := ∫ x, HRS.Whole.projMean mu phi x ^ 2 ∂mu
  let V0 : ℝ := ∫ x, HRS.Whole.projMean mu (f 0) x ^ 2 ∂mu
  let B : ℝ := HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta (f 0) (f 0)
  let G : ℝ := HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma (f 0) (f 0)
  let N : ℝ := noiseCovW C beta⁻¹ t t phi phi
  have hV0 : 0 ≤ V0 := integral_nonneg fun x => sq_nonneg _
  have hGupper : G ≤ V0 := (hRFgamma.coercive _ hf0).2
  have hGlower : etag * V0 ≤ G := (hRFgamma.coercive _ hf0).1
  have hB : eta * V0 ≤ B := (hRFbeta.coercive _ hf0).1
  have hterminal : HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta phi phi ≤ V :=
    (hRFbeta.coercive _ hphim).2
  have hN : 0 ≤ N := by
    unfold N noiseCovW
    refine mul_nonneg (by positivity) (integral_nonneg fun r => ?_)
    refine integral_nonneg fun x => mul_nonneg real_inner_self_nonneg ?_
    exact hrho.1.1.nonneg x
  have hbalance : B + N = HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta phi phi := by
    have hq := s111x2_quench_ge (γ := beta) hd hs0 hs ha hbeta hrho ht le_rfl hf hf
    have hft : propagatorW C t t phi = phi := hf.terminal
    change B + N = HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta phi
      (propagatorW C t t phi) + B - B at hq
    rw [hft] at hq
    linarith
  change 0 ≤ G + N ∧ G + N ≤ eta⁻¹ * V
  constructor
  · exact add_nonneg ((mul_nonneg hetag.le hV0).trans hGlower) hN
  · have hscaled : eta * (G + N) ≤ V := by
      calc
        eta * (G + N) = eta * G + eta * N := by ring
        _ ≤ B + N := add_le_add
          ((mul_le_mul_of_nonneg_left hGupper heta.le).trans hB)
          (mul_le_of_le_one_left hN heta1)
        _ = HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta phi phi := hbalance
        _ ≤ V := hterminal
    calc
      G + N ≤ V / eta := (le_div_iff₀ heta).2 (by nlinarith [hscaled])
      _ = eta⁻¹ * V := by ring

end HRS.MS.ProClosureS111
