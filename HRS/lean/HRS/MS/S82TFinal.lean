import HRS.MS.S82TBVar
import HRS.MS.S82TJVar
import HRS.MS.S82TJ
import HRS.MS.S82TB
import HRS.MS.S82TAe
import HRS.MS.QsfCorr2

/-!
# S8.2 R06: weighted repeated-pair moments (frozen statement of the Pro skeleton `S82.R06`)
The frozen kernels `pairJ`, `repeatedB` are replaced, off the diagonal and hence almost surely under the physical
canonical law, by explicit jointly measurable symmetric models (`S82TJ`, `S82TB`); the row bounds come from
`s82q_pair_template` (`S82TJRow`, `S82TBRow`), the transfer to `canonicalP` from domination.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- The repeated-pair variance, with actual expectation subtraction, and the canonical J-pair variance. -/
theorem weighted_repeated_pair_moments (d : ℕ) (hd : 2 ≤ d)
    (a beta M C0 C1 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (pairStatistic (N := N) (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q))
          2 (canonicalP d N a beta) ∧
        MemLp (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSum (repeatedB rho Q) X) 2 (canonicalP d N a beta) ∧
        evariance (pairStatistic (N := N)
          (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q)) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 * logN N / N) ∧
        evariance (fun X : EucConfig d N =>
          (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSum (repeatedB rho Q) X) (canonicalP d N a beta) ≤
            ENNReal.ofReal (C * A ^ 2 / N) := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  have hρ0 : HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) := hT.prob
  have hρG : HRS.Whole.HasR2GaussianUpper (Cth + 1) cth
      (HRS.Whole.thermalDensity d (criticalS d) a beta) := by
    refine ⟨hT.hc, fun x => ?_⟩
    have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  have hG : 0 < Cth + 1 := by linarith [hT.C0]
  obtain ⟨Kf, hKf0, hFmm, hKf⟩ := HRS.MS.S82T.s82t_forceMean_bdd hd ha hbeta
  obtain ⟨CJ, hCJ0, hJ⟩ := HRS.MS.S82T.s82t_J_variance hd (a := a) (C0 := C0) (C1 := C1) hM hbeta q hq
    (rho := HRS.Whole.thermalDensity d (criticalS d) a beta) (Cth + 1) cth hG hT.hc hρ0 hρG
  obtain ⟨CB, hCB0, hB⟩ := HRS.MS.S82T.s82t_B_variance hd (a := a) (C0 := C0) hM hbeta q hq
    (rho := HRS.Whole.thermalDensity d (criticalS d) a beta) (Cth + 1) cth hG hT.hc hρ0 hρG
  have hσ0 : 0 ≤ HRS.Whole.movtr_sigma (criticalS d) := HRS.MS.S82T.s82t_sigma_nonneg _ hs0
  set Cb : ℝ := 2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * Kf with hCb
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  refine ⟨CJ + CB * Cb ^ 2, by positivity, ?_⟩
  intro rho hrho h hW hP f A hA Q hQ N hN
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal
      (HRS.Whole.thermalDensity d (criticalS d) a beta)) := HRS.Whole.Q09A.measure_isProb hρ0
  set rho := HRS.Whole.thermalDensity d (criticalS d) a beta with hrhodef
  set mu := HRS.Whole.withDensityReal rho with hmudef
  have hC0 := hW.positive
  have hNr : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL1 := HRS.MS.S82Q.s82q_logN_nonneg (N := N) (by omega)
  have hL0 : 0 ≤ logN N := by linarith
  have hae := HRS.MS.S82T.s82t_ae_noncollision hd hW hN
  -- the J part
  have hρm : Measurable ((critCoeff d a beta rho).ρ 0) := hρ0.measurable
  set Jt := HRS.MS.S82T.s82t_Jt (critCoeff d a beta rho) mu (HRS.MS.S82P2.s82p2_gt Q) with hJt
  have hJm : Measurable (Function.uncurry Jt) :=
    HRS.MS.S82T.s82t_Jt_measurable (critCoeff d a beta rho) mu hρm
      (HRS.MS.S82P2.s82p2_gt_measurable Q)
  have hJae : ∀ x : Euc d, (pairJ (critCoeff d a beta rho) mu Q x) =ᵐ[mu] Jt x := fun x =>
    (HRS.MS.S82T.s82t_mu_ae_ne hd rho x).mono fun y hy =>
      HRS.MS.S82T.s82t_pairJ_eq hd hQ x y (Ne.symm hy)
  have hnl := hQ.nonlocal
  obtain ⟨hJM, hJV⟩ := hJ h hW hP A hA Jt hJm (HRS.MS.S82T.s82t_Jt_symm _ _ _)
    (fun x y hxy => by
      rw [hJt, ← HRS.MS.S82T.s82t_pairJ_eq hd hQ x y hxy]
      exact hnl.2 x y hxy)
    (fun x => (hnl.1.2.1 x).congr (hJae x))
    (fun x => (integral_congr_ae (hJae x).symm).trans (hnl.1.2.2.2 x)) N hN
  have hJeq : (pairStatistic (N := N) (pairJ (critCoeff d a beta rho) mu Q)) =ᵐ[canonicalP d N a beta]
      (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSum Jt X) :=
    hae.mono fun X hX => by
      beta_reduce
      unfold pairStatistic
      rw [HRS.MS.S82T.s82t_pairSum_congr hX
        (fun x y hxy => HRS.MS.S82T.s82t_pairJ_eq hd hQ x y hxy)]
  -- the B part
  have hBm : Measurable (Function.uncurry (HRS.MS.S82T.s82t_B0 (forceMean rho) (HRS.MS.S82P2.s82p2_gt Q))) :=
    HRS.MS.S82T.s82t_B0_measurable hFmm (HRS.MS.S82P2.s82p2_gt_measurable Q)
  obtain ⟨hBM, hBV⟩ := hB h hW (Cb * A) (by positivity)
    (HRS.MS.S82T.s82t_B0 (forceMean rho) (HRS.MS.S82P2.s82p2_gt Q)) hBm
    (HRS.MS.S82T.s82t_B0_symm _ _)
    (fun x y hxy => by
      have := HRS.MS.S82T.s82t_B0_bound hd hQ hA hKf0 hKf x y hxy
      calc _ ≤ _ := this
        _ = _ := by ring) N hN
  have hBeq : (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * pairSum (repeatedB rho Q) X)
      =ᵐ[canonicalP d N a beta]
      (fun X : EucConfig d N => ((N : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) *
        pairSum (HRS.MS.S82T.s82t_B0 (forceMean rho) (HRS.MS.S82P2.s82p2_gt Q)) X) :=
    hae.mono fun X hX => by
      beta_reduce
      rw [HRS.MS.S82T.s82t_pairSum_congr hX
        (fun x y hxy => HRS.MS.S82T.s82t_repeatedB_eq hQ x y hxy)]
  refine ⟨hJM.ae_eq hJeq.symm, hBM.ae_eq hBeq.symm, ?_, ?_⟩
  · rw [evariance_congr hJeq]
    refine hJV.trans (ENNReal.ofReal_le_ofReal ?_)
    calc CJ * A ^ 2 * logN N / N
        ≤ CJ * A ^ 2 * logN N / N + CB * Cb ^ 2 * A ^ 2 * logN N / N :=
          le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  · rw [evariance_congr hBeq]
    refine hBV.trans (ENNReal.ofReal_le_ofReal ?_)
    calc CB * (Cb * A) ^ 2 / N = CB * Cb ^ 2 * A ^ 2 / N := by ring
      _ ≤ CB * Cb ^ 2 * A ^ 2 / N + CJ * A ^ 2 / N :=
          le_add_of_nonneg_right (by positivity)
      _ = _ := by ring

end HRS.MS.Phase2S82
