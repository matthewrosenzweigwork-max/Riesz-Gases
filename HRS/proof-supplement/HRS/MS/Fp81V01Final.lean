import HRS.MS.Fp81V01PairedVariation
import HRS.MS.Fp81V01DifferenceWindow
import HRS.MS.Fp81V01WindowMoments
import HRS.MS.Fp81V01Evaluations
import HRS.MS.Fp81V01GivenTensor
import HRS.MS.ProClosureS111PairedInitial
import HRS.MS.S111K4Asm

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.S111T HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81v01_final_weighted_integral_mono
    (u H κ csmall cbig A B : ℝ)
    (hB : 0 ≤ B) (hAB : A ≤ B) (hcc : csmall ≤ cbig) :
    A * (∫ t in Icc 0 H,
      Real.exp (-cbig * max (u - t) 0) * Real.exp (-κ * t)) ≤
    B * (∫ t in Icc 0 H,
      Real.exp (-csmall * max (u - t) 0) * Real.exp (-κ * t)) := by
  let fbig : ℝ → ℝ := fun t =>
    Real.exp (-cbig * max (u - t) 0) * Real.exp (-κ * t)
  let fsmall : ℝ → ℝ := fun t =>
    Real.exp (-csmall * max (u - t) 0) * Real.exp (-κ * t)
  have hbigI : IntegrableOn fbig (Icc 0 H) := by
    have hc : Continuous fbig := by
      dsimp [fbig]
      fun_prop
    exact hc.continuousOn.integrableOn_Icc
  have hsmallI : IntegrableOn fsmall (Icc 0 H) := by
    have hc : Continuous fsmall := by
      dsimp [fsmall]
      fun_prop
    exact hc.continuousOn.integrableOn_Icc
  have hcmp : (∫ t in Icc 0 H, fbig t) ≤ (∫ t in Icc 0 H, fsmall t) := by
    apply setIntegral_mono_on hbigI hsmallI measurableSet_Icc
    intro t ht
    have hage : 0 ≤ max (u - t) 0 := le_max_right _ _
    have hcoef : csmall * max (u - t) 0 ≤ cbig * max (u - t) 0 :=
      mul_le_mul_of_nonneg_right hcc hage
    have hexp : Real.exp (-cbig * max (u - t) 0) ≤
        Real.exp (-csmall * max (u - t) 0) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [fbig, fsmall]
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have hbig0 : 0 ≤ ∫ t in Icc 0 H, fbig t :=
    setIntegral_nonneg measurableSet_Icc fun t _ =>
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc
    A * (∫ t in Icc 0 H, fbig t) ≤ B * (∫ t in Icc 0 H, fbig t) :=
      mul_le_mul_of_nonneg_right hAB hbig0
    _ ≤ B * (∫ t in Icc 0 H, fsmall t) := mul_le_mul_of_nonneg_left hcmp hB

/-- The physical source contract V01, with constants selected before the thermal density. -/
theorem fp81v01_physical_V01 {d : ℕ} (hd : 2 ≤ d)
    (s a β γ T lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hT : 0 < T) (hlam : 0 < lam) :
    HRS.MS.S111T.S111tV01 d s a β γ T lam := by
  let rho0 : Euc d → ℝ := thermalDensity d s a β
  have hsd : s < (d : ℝ) := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  by_cases hex : IsThermalEquilibrium d s a β rho0 ∧
      IsR2Poincare (HRS.Whole.withDensityReal rho0) lam
  · obtain ⟨hrho0, hgap0⟩ := hex
    obtain ⟨M0, hM0, hMarginal⟩ := canonical_window_L4
      hd hs0 hs ha hβ hγ hT rho0 hrho0
    obtain ⟨M1, hM1, hDifference⟩ := fp81v01_difference_canonical_window_L4
      hd hs0 hs ha hβ hγ hT hlam rho0 hrho0 hgap0
    let M : ℝ := max M0 M1
    have hM : 0 < M := lt_of_lt_of_le hM0 (le_max_left _ _)
    have hM0M : M0 ≤ M := le_max_left _ _
    have hM1M : M1 ≤ M := le_max_right _ _
    obtain ⟨E, cR, BR, R, hcR, hBR, hR, hresponses⟩ :=
      physical_paired_interval_responses hd s a β T lam hs0 hs ha hβ hT hlam
    obtain ⟨cI, BI, hcI, hBI, hInitial⟩ :=
      physical_paired_initial_tensors hd s a β γ T hs0 hs ha hβ hγ hT
    let c0 : ℝ := min cI cR
    have hc0 : 0 < c0 := lt_min hcI hcR
    have hc0I : c0 ≤ cI := min_le_left _ _
    have hc0R : c0 ≤ cR := min_le_right _ _
    let κ : ℝ := lam / β
    have hκ : 0 < κ := by dsimp [κ]; exact div_pos hlam hβ
    let ν : ℝ := (r26t6_thermalCoeff d s a β rho0).ν
    let BD : ℝ := 3 * BR * R * M ^ 2 * (1 + 2 * Real.exp (κ * T))
    let BJ : ℝ := 3 * BR * |2 * ν| * R * M * (1 + Real.exp (κ * T))
    have hBD : 0 ≤ BD := by dsimp [BD]; positivity
    have hBJ : 0 ≤ BJ := by dsimp [BJ]; positivity
    let B : ℝ := max (max BI BD) BJ
    have hB : 0 ≤ B := by
      dsimp [B]
      exact hBJ.trans (le_max_right _ _)
    have hBInit : BI ≤ B := by
      dsimp [B]
      calc
        BI ≤ max BI BD := le_max_left _ _
        _ ≤ max (max BI BD) BJ := le_max_left _ _
    have hBDMax : BD ≤ B := by
      dsimp [B]
      calc
        BD ≤ max BI BD := le_max_right _ _
        _ ≤ max (max BI BD) BJ := le_max_left _ _
    have hBJMax : BJ ≤ B := by dsimp [B]; exact le_max_right _ _
    refine ⟨c0, B, hc0, hB, ?_⟩
    intro rho hrho hgap u hu Ku Kb hKu hKb
    have hrhoEq : rho = rho0 := by
      dsimp [rho0]
      exact HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hrho
    subst rho
    obtain ⟨Iu, Ib, hIu, hIb, hIdiff⟩ := hInitial rho0 hrho0 u hu
    have hH0 : 0 ≤ u + T := add_nonneg hu hT.le
    have hPw : (d : ℝ) < 2 * r26t6_coreWeight d := by
      unfold r26t6_coreWeight
      have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    obtain ⟨P, hprob, hLaw, basis, hbasis, qLin, qQuad, hfields, O,
      hcontrols, hΔL, hΔQ⟩ := hresponses rho0 hrho0 hgap0 γ hγ u hu
    letI : IsProbabilityMeasure P := hprob
    let Z : Fin 2 → PathPair d (wholeSpaceIndex d) (u + T) → R2X d T :=
      fun i w => physicalPairedWindow hu le_rfl i w
    have hMom : ∀ i : Fin 2, MemLp (Z i) 4 P ∧
        eLpNorm (Z i) 4 P ≤ ENNReal.ofReal M := by
      intro i
      have h := hMarginal u hu P hLaw i
      refine ⟨?_, ?_⟩
      · simpa [Z] using h.1
      · simpa [Z] using h.2.trans (ENNReal.ofReal_le_ofReal hM0M)
    have hΔZ : MemLp (fun w => Z 0 w - Z 1 w) 4 P ∧
        eLpNorm (fun w => Z 0 w - Z 1 w) 4 P ≤
          ENNReal.ofReal (M * Real.exp (-κ * u)) := by
      have h := hDifference u hu P hLaw
      refine ⟨?_, ?_⟩
      · simpa [Z] using h.1
      · have hbound := h.2.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hM1M (Real.exp_pos _).le))
        simpa [Z, κ] using hbound
    have hqL : MemLp (qLin 1) 2 ((volume.restrict (Icc 0 (u + T))).prod P) :=
      (hfields 1).linear_moment
    have hqQ : MemLp (qQuad 1) 2 ((volume.restrict (Icc 0 (u + T))).prod P) :=
      (hfields 1).quadratic_moment
    have hcontract0 : r26t6_SourceContractions P s a β γ rho0 T u (Z 0)
        (fun t w f => inner ℝ (qQuad 0 (t, w)) (E.encode f))
        (fun t w f => inner ℝ (qLin 0 (t, w)) (E.encode f)) := by
      have h := physical_source_contractions_of_fields hd hs0 hs ha hβ hγ hu le_rfl
        hH0 hPw hrho0 P hLaw E 0 basis hbasis (qLin 0) (qQuad 0) (hfields 0)
      simpa [r26t6_preparation, Z] using h
    have hcontract1 : r26t6_SourceContractions P s a β β rho0 T u (Z 1)
        (fun t w f => inner ℝ (qQuad 1 (t, w)) (E.encode f))
        (fun t w f => inner ℝ (qLin 1 (t, w)) (E.encode f)) := by
      have h := physical_source_contractions_of_fields hd hs0 hs ha hβ hγ hu le_rfl
        hH0 hPw hrho0 P hLaw E 1 basis hbasis (qLin 1) (qQuad 1) (hfields 1)
      simpa [r26t6_preparation, Z] using h
    obtain ⟨Iu', hIu', hIu'D, hIu'J⟩ := cumulative_sources
      hu hT hcR hBR R M hR.le hM.le P O (qLin 0) (qQuad 0) (Z 0)
      (hcontrols 0).1 (hcontrols 0).2 (hMom 0) Iu
    let K0 : projTensor (R2X d T) 3 :=
      Iu + D P O (qQuad 0) (Z 0) (u + T) + J P O (qLin 0) (Z 0) (u + T)
    obtain ⟨S0, hS0⟩ := physical_evaluations P O (qLin 0) (qQuad 0) (Z 0)
      (fun _ => R) (fun _ => R) (hcontrols 0).1 (hcontrols 0).2 (hMom 0).1
      hcontract0 Iu K0 hIu Iu' hIu' hIu'D hIu'J
    have hS0initial : S0.initial = Iu := by
      change S0.toCubicSources.initial = Iu
      rw [hS0]
      exact hIu'
    have hS0drift : S0.drift = D P O (qQuad 0) (Z 0) := by
      change S0.toCubicSources.drift = D P O (qQuad 0) (Z 0)
      rw [hS0]
      exact hIu'D
    have hS0cov : S0.covariance = J P O (qLin 0) (Z 0) := by
      change S0.toCubicSources.covariance = J P O (qLin 0) (Z 0)
      rw [hS0]
      exact hIu'J
    have hK0 : Ku = K0 := fp81v01_given_tensor_eq hT hu hKu S0
    subst Ku
    obtain ⟨Ib', hIb', hIb'D, hIb'J⟩ := cumulative_sources
      hu hT hcR hBR R M hR.le hM.le P O (qLin 1) (qQuad 1) (Z 1)
      (hcontrols 1).1 (hcontrols 1).2 (hMom 1) Ib
    let K1 : projTensor (R2X d T) 3 :=
      Ib + D P O (qQuad 1) (Z 1) (u + T) + J P O (qLin 1) (Z 1) (u + T)
    obtain ⟨S1, hS1⟩ := physical_evaluations P O (qLin 1) (qQuad 1) (Z 1)
      (fun _ => R) (fun _ => R) (hcontrols 1).1 (hcontrols 1).2 (hMom 1).1
      hcontract1 Ib K1 hIb Ib' hIb' hIb'D hIb'J
    have hS1initial : S1.initial = Ib := by
      change S1.toCubicSources.initial = Ib
      rw [hS1]
      exact hIb'
    have hS1drift : S1.drift = D P O (qQuad 1) (Z 1) := by
      change S1.toCubicSources.drift = D P O (qQuad 1) (Z 1)
      rw [hS1]
      exact hIb'D
    have hS1cov : S1.covariance = J P O (qLin 1) (Z 1) := by
      change S1.toCubicSources.covariance = J P O (qLin 1) (Z 1)
      rw [hS1]
      exact hIb'J
    have hK1 : Kb = K1 := fp81v01_given_tensor_eq hT hu hKb S1
    subst Kb
    have hPaired := paired_variation hu hT hcR hBR κ R M hκ hR.le hM.le P O
      qLin qQuad Z hcontrols hΔL hΔQ hqL hqQ hMom hΔZ
    have hκDef : κ = lam / β := rfl
    have hInitialBound : ‖S0.initial - S1.initial‖ ≤ B * Real.exp (-3 * c0 * u) := by
      rw [hS0initial, hS1initial]
      have hExp : Real.exp (-3 * cI * u) ≤ Real.exp (-3 * c0 * u) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_right hc0I (show 0 ≤ 3 * u by positivity)
        nlinarith
      calc
        ‖Iu - Ib‖ ≤ BI * Real.exp (-3 * cI * u) := hIdiff
        _ ≤ BI * Real.exp (-3 * c0 * u) :=
          mul_le_mul_of_nonneg_left hExp hBI
        _ ≤ B * Real.exp (-3 * c0 * u) :=
          mul_le_mul_of_nonneg_right hBInit (Real.exp_pos _).le
    have hDriftBound : eVariationOn (fun v => S0.drift v - S1.drift v)
        (Icc 0 (u + T)) ≤ ENNReal.ofReal
          (B * ∫ t in Icc 0 (u + T),
            Real.exp (-c0 * max (u - t) 0) * Real.exp (-κ * t)) := by
      rw [hS0drift, hS1drift]
      have hraw : eVariationOn
          (fun v => D P O (qQuad 0) (Z 0) v - D P O (qQuad 1) (Z 1) v)
          (Icc 0 (u + T)) ≤ ENNReal.ofReal
            (BD * ∫ t in Icc 0 (u + T),
              Real.exp (-cR * max (u - t) 0) * Real.exp (-κ * t)) := by
        simpa [BD, ν, κ] using hPaired.1
      exact hraw.trans (ENNReal.ofReal_le_ofReal
        (fp81v01_final_weighted_integral_mono u (u + T) κ c0 cR BD B
          hB hBDMax hc0R))
    have hCovBound : eVariationOn (fun v => S0.covariance v - S1.covariance v)
        (Icc 0 (u + T)) ≤ ENNReal.ofReal
          (B * ∫ t in Icc 0 (u + T),
            Real.exp (-2 * c0 * max (u - t) 0) * Real.exp (-κ * t)) := by
      rw [hS0cov, hS1cov]
      have hraw : eVariationOn
          (fun v => J P O (qLin 0) (Z 0) v - J P O (qLin 1) (Z 1) v)
          (Icc 0 (u + T)) ≤ ENNReal.ofReal
            (BJ * ∫ t in Icc 0 (u + T),
              Real.exp (-2 * cR * max (u - t) 0) * Real.exp (-κ * t)) := by
        simpa [BJ, ν, κ] using hPaired.2
      have hweight := fp81v01_final_weighted_integral_mono
        u (u + T) κ (2 * c0) (2 * cR) BJ B hB hBJMax
        (mul_le_mul_of_nonneg_left hc0R (by norm_num))
      have hweight' : BJ * (∫ t in Icc 0 (u + T),
            Real.exp (-2 * cR * max (u - t) 0) * Real.exp (-κ * t)) ≤
          B * (∫ t in Icc 0 (u + T),
            Real.exp (-2 * c0 * max (u - t) 0) * Real.exp (-κ * t)) := by
        convert hweight using 1 <;>
          simp only [show -(2 * cR) = -2 * cR by ring,
            show -(2 * c0) = -2 * c0 by ring]
      exact hraw.trans (ENNReal.ofReal_le_ofReal
        hweight')
    exact ⟨S0, S1, hInitialBound, by simpa [hκDef] using hDriftBound,
      by simpa [hκDef] using hCovBound⟩
  · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    intro rho hrho hgap u hu Ku Kb hKu hKb
    have hrhoEq : rho = rho0 := by
      dsimp [rho0]
      exact HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hrho
    subst rho
    exfalso
    exact hex ⟨hrho, hgap⟩

/-- The V01 contract for every admissible frozen parameter tuple. -/
theorem fp81v01_K4V01All : HRS.MS.S111K4.K4V01All := by
  intro d hd s a β γ T lam hs0 hs ha hβ hγ hT hlam
  exact fp81v01_physical_V01 hd s a β γ T lam hs0 hs ha hβ hγ hT hlam

/-- The frozen tensor relaxation follows from V01 and the accepted V02 contract. -/
theorem fp81v01_tensor_relaxation : type_of% @HRS.Whole.r2_tensor_relaxation :=
  HRS.MS.S111K4.k4_tensor_relaxation_of_V01 fp81v01_K4V01All

/-- The frozen two-parameter Edgeworth statement uses V01 at both preparations. -/
theorem fp81v01_two_parameter_edgeworth :
    type_of% @HRS.Whole.r2_two_parameter_edgeworth := by
  intro d hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
  exact HRS.MS.S111T.s111t_two_param_of_producers hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (fp81v01_physical_V01 hd s a β γ T lam hs0 hs ha hβ hγ hT hlam)
    (fp81v01_physical_V01 hd s a β β T lam hs0 hs ha hβ hβ.le hT hlam)
    (HRS.MS.S111K4.k4_v02_contract hd s hs0 hs a β ha hβ T)

#print axioms fp81v01_physical_V01
#print axioms fp81v01_K4V01All
#print axioms fp81v01_tensor_relaxation
#print axioms fp81v01_two_parameter_edgeworth

end HRS.Fp81.V01
