import HRS.MS.ProClosureS111LogResponse
import HRS.MS.R26T6CI01
import HRS.MS.R26T6CI06
import HRS.MS.R26T6CI07MomentAux
import HRS.MS.S111X2Aux5

/-!
Physical thermal screening on L³ and its Lipschitz third-moment estimate,
including the logarithmic kernel and the zero preparation parameter.
Uniform constants are chosen before the thermal density and before the
preparation parameter in the specified closed interval.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.R26T6C HRS.MS.S111X2

variable {d : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem physical_kernel_L2_L3 (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ,
      MemLp f 2 (HRS.Whole.withDensityReal rho) →
      MemLp (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal rho) f) 3 (HRS.Whole.withDensityReal rho) ∧
      eLpNorm (HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal rho) f) 3 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal C * eLpNorm f 2 (HRS.Whole.withDensityReal rho) := by
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  obtain ⟨M, c, S, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho
  have hM := HRS.MS.TcR.tc2_le_M0 hTc.prob hc hTc.gauss
  rcases hs0.eq_or_lt with hzero | hpos
  · subst s
    have hm3 := (r26t6c_gaussian_moments rho hTc.prob M c hc hTc.gauss 3).2
    have hn3 : MemLp (fun x : Euc d => ‖x‖) 3 (HRS.Whole.withDensityReal rho) :=
      r26t6c_memLp_three_of_integrable_cube (HRS.Whole.withDensityReal rho) (fun x => ‖x‖)
        measurable_norm (by simpa only [abs_norm] using hm3)
    exact logarithmic_Kop_L2_L3 hd rho hTc.prob M hM hn3
  · refine ⟨2 * Real.sqrt (M * sphereArea d / ((d : ℝ) - 2 * s) + 1),
      by positivity, fun f hf => ?_⟩
    exact r26t6c_positive_riesz_Kop_L2_L3 hd s M hpos (by linarith) rho hTc.prob hM f hf

/-- The physical response as an actual L³ continuous linear map; the bound is
uniform in the equilibrium density and valid for every nonnegative preparation. -/
theorem physical_response_L3_CLM_uniform (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma : ℝ, 0 ≤ gamma →
      ∃ R : Lp ℝ 3 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 3 (HRS.Whole.withDensityReal rho),
        ‖R‖ ≤ 2 * (1 + gamma * C) ∧
        ∀ f : Euc d → ℝ, ∀ hf : MemLp f 3 (HRS.Whole.withDensityReal rho),
          (R (hf.toLp f) : Euc d → ℝ) =ᵐ[HRS.Whole.withDensityReal rho]
            HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f := by
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  by_cases hex : ∃ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho
  · obtain ⟨rho0, hrho0⟩ := hex
    obtain ⟨C, hC, h23⟩ := physical_kernel_L2_L3 hd hs0 hs ha hbeta hrho0
    obtain ⟨M, c, S, hc, hTc⟩ :=
      HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho0
    letI : IsProbabilityMeasure (HRS.Whole.withDensityReal rho0) := Q34.isProbabilityMeasure_nu hTc.prob
    obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
    refine ⟨C, hC, fun rho hrho gamma hgamma => ?_⟩
    have heq : rho = rho0 := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho).trans
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho0).symm
    subst rho
    exact r26t6c_response_L3_CLM (HRS.Whole.withDensityReal rho0) (rieszKernel d s)
      K Mg C hC hK h23 gamma hgamma
  · exact ⟨0, le_rfl, fun rho hrho => False.elim (hex ⟨rho, hrho⟩)⟩

theorem response_lipschitz_third (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (kernel : Euc d → ℝ) (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (Mg C : ℝ) (hC : 0 ≤ C) (hK : KRep kernel mu K Mg)
    (h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop kernel mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop kernel mu f) 3 mu ≤ ENNReal.ofReal C * eLpNorm f 2 mu)
    (hm3 : Integrable (fun x : Euc d => ‖x‖ ^ 3) mu)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (f : Euc d → ℝ)
    (L : ℝ≥0) (hL : LipschitzWith L f) :
    let h := HRS.Whole.responseInverse kernel mu gamma f
    Integrable (fun x => |h x| ^ 3) mu ∧
      (∫ x, |h x| ^ 3 ∂mu) ≤
        (1 + gamma * C) ^ 3 * (8 * (L : ℝ) ^ 3 * ∫ x, ‖x‖ ^ 3 ∂mu) := by
  let B : ℝ := 1 + gamma * C
  let h := HRS.Whole.responseInverse kernel mu gamma f
  let p := HRS.Whole.projMean mu f
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpCube := r26t6c_centered_lipschitz_third mu hm3 f L hL
  have hp3 : MemLp p 3 mu := r26t6c_memLp_three_of_integrable_cube mu p
    (hL.continuous.measurable.sub measurable_const) hpCube.1
  have hf3 : MemLp f 3 mu := by
    have hsum := hp3.add (memLp_const (HRS.Whole.pair mu f))
    convert hsum using 1
    funext x
    simp [p, HRS.Whole.projMean]
  have hres := r26t6c_response_L3 mu kernel K Mg C hC hK h23 gamma hgamma f hf3
  have htop : ENNReal.ofReal B * eLpNorm p 3 mu ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hp3).ne
  have hnorm : lpNorm h 3 mu ≤ B * lpNorm p 3 mu := by
    have hreal := ENNReal.toReal_mono htop hres.2
    simpa only [h, B, p, toReal_eLpNorm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hB] using hreal
  have hcube : (∫ x, |h x| ^ 3 ∂mu) ≤ B ^ 3 * ∫ x, |p x| ^ 3 ∂mu := by
    have hh := pow_le_pow_left₀ (lpNorm_nonneg (f := h) (p := (3 : ENNReal))) hnorm 3
    rw [r26t6c_lpNorm_three_pow mu h hres.1, mul_pow,
      r26t6c_lpNorm_three_pow mu p hp3] at hh
    exact hh
  refine ⟨?_, hcube.trans (mul_le_mul_of_nonneg_left hpCube.2 (pow_nonneg hB _))⟩
  simpa only [Real.norm_eq_abs] using
    hres.1.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)

/-- The full thermal screened third moment, including `s = 0` and `gamma = 0`. -/
theorem physical_screened_lipschitz_third_uniform (hd : 2 ≤ d)
    (s a beta Gamma : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hGamma : 0 ≤ Gamma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho → ∀ gamma ∈ Icc (0 : ℝ) Gamma,
      ∀ f : Euc d → ℝ, ∀ L : ℝ≥0, LipschitzWith L f →
      Integrable (fun x => |HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f x| ^ 3)
        (HRS.Whole.withDensityReal rho) ∧
      (∫ x, |HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f x| ^ 3
        ∂HRS.Whole.withDensityReal rho) ≤ B * (L : ℝ) ^ 3 := by
  have hsd : s < (d : ℝ) := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  by_cases hex : ∃ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho
  · obtain ⟨rho0, hrho0⟩ := hex
    obtain ⟨C, hC, h23⟩ := physical_kernel_L2_L3 hd hs0 hs ha hbeta hrho0
    obtain ⟨M, c, S, hc, hTc⟩ :=
      HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hrho0
    let mu := HRS.Whole.withDensityReal rho0
    letI : IsProbabilityMeasure mu := Q34.isProbabilityMeasure_nu hTc.prob
    obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
    have hm3 : Integrable (fun x : Euc d => ‖x‖ ^ 3) mu :=
      (r26t6c_gaussian_moments rho0 hTc.prob M c hc hTc.gauss 3).2
    have hmoment : 0 ≤ ∫ x : Euc d, ‖x‖ ^ 3 ∂mu := integral_nonneg fun x => by positivity
    let B : ℝ := (1 + Gamma * C) ^ 3 * (8 * ∫ x : Euc d, ‖x‖ ^ 3 ∂mu)
    refine ⟨B, by dsimp [B]; positivity, fun rho hrho gamma hgamma f L hL => ?_⟩
    have heq : rho = rho0 := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho).trans
      (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho0).symm
    subst rho
    have h := response_lipschitz_third mu (rieszKernel d s) K Mg C hC hK h23
      hm3 gamma hgamma.1 f L hL
    refine ⟨h.1, h.2.trans ?_⟩
    have hmono : 1 + gamma * C ≤ 1 + Gamma * C :=
      by nlinarith [mul_le_mul_of_nonneg_right hgamma.2 hC]
    calc
      _ ≤ (1 + Gamma * C) ^ 3 * (8 * (L : ℝ) ^ 3 * ∫ x : Euc d, ‖x‖ ^ 3 ∂mu) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (add_nonneg (by norm_num)
            (mul_nonneg hgamma.1 hC)) hmono 3) (by positivity)
      _ = B * (L : ℝ) ^ 3 := by dsimp [B]; ring
  · exact ⟨0, le_rfl, fun rho hrho => False.elim (hex ⟨rho, hrho⟩)⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_kernel_L2_L3
#print axioms HRS.MS.ProClosureS111.physical_response_L3_CLM_uniform
#print axioms HRS.MS.ProClosureS111.physical_screened_lipschitz_third_uniform
