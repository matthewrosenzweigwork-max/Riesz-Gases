import HRS.MS.R2SeAux48

/-!
# S9.9 `r2_static_edgeworth`: proof of the frozen statement `HRS.Whole.r2_static_edgeworth`

Worker S99.  `round2_static_edgeworth_proof : type_of% @HRS.Whole.r2_static_edgeworth` (tie in `R2SeTie.lean`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

set_option maxHeartbeats 4000000 in
theorem round2_static_edgeworth_proof : type_of% @HRS.Whole.r2_static_edgeworth := by
  intro d s hd hs0 hs a β γ ha hβ hγ m hm ρ hρ
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hd1 : 1 ≤ d := by omega
  have hρeq := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  unfold R2StaticEdgeworth
  obtain ⟨C, c, BU, hT⟩ := s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨Cs, -, hSall⟩ := S46.s46_static_all hd hs0 hsd (am := a) (ap := a) (βm := β) (βp := β) (γm := γ)
    (γp := γ) ha hβ hγ le_rfl le_rfl le_rfl
  have hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N := fun N hN =>
    hSall a ⟨le_rfl, le_rfl⟩ β ⟨le_rfl, le_rfl⟩ γ ⟨le_rfl, le_rfl⟩ N hN
  obtain ⟨e⟩ := s45_exists_enum hd1
  have hmJ : ((J1 d : ℕ) : ℝ) + 2 * d < (m : ℝ) := by
    unfold J1; push_cast at hm ⊢; linarith
  have hmd : (d : ℝ) < (m : ℝ) := by
    have : (0 : ℝ) ≤ ((J1 d : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    linarith
  set φ : ℕ → Euc d → ℝ := fun j => oscTestFun (m : ℝ) (e j) with hφdef
  have hφ : IsSummableFeatureFamily (J1 d) φ := s45_summable_oscTest hd1 (J1 d) hmJ e
  obtain ⟨F⟩ := s99_famData hd hs0 hsd ha hβ hγ hφ.1
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  -- the Gaussian
  obtain ⟨L, hL⟩ := s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨-, G', hG'⟩ := exists_gaussian_feature_proof hd hs0 hsd (J1 d) (J1_gt d) (thermalDensity d s a β)
    hT.prob C hM γ hγ φ hφ L (fun _ => hL)
  haveI hGG : ProbabilityTheory.IsGaussian G' := hG'.1.1
  have hmemH : ∀ α : MultiIndex d, MemLp (hermiteFunD α) 2 (thermalMeasure d s a β) := by
    intro α
    obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
    exact MemLp.of_bound (contDiff_hermiteFunD α).continuous.aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC0 α x)
  have hG'' : IsCenteredGaussianSeq G' fun i j => oscEigenvalue d (e i) ^ (-((m : ℝ) / 2)) *
      oscEigenvalue d (e j) ^ (-((m : ℝ) / 2)) * susceptibilityCov (rieszKernel d s)
        (withDensityReal (thermalDensity d s a β)) γ (hermiteFunD (e i)) (hermiteFunD (e j)) := by
    convert hG' using 3 with i j
    exact (S46.s46_cov_smul hd hs0 hsd hγ hT (hmemH (e i)) (hmemH (e j))
      (oscEigenvalue d (e i) ^ (-((m : ℝ) / 2))) (oscEigenvalue d (e j) ^ (-((m : ℝ) / 2)))).symm
  have hΨm : Measurable (s45_Psi (m : ℝ) e).symm := (s45_Psi (m : ℝ) e).symm.continuous.measurable
  haveI hGprob : IsProbabilityMeasure (G'.map (s45_Psi (m : ℝ) e).symm) :=
    ⟨by rw [Measure.map_apply hΨm MeasurableSet.univ]; simp⟩
  have hell : ∀ x, r2EllPt (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) γ m x =
      (s45_Psi (m : ℝ) e).symm (ellv d s a β γ φ x) := s99_ell_eq hd hs0 hs ha hβ hγ hT m e hφ F
  have hellc := s99_ellv_cont hd hs0 hs ha hβ hγ hT hφ F
  refine ⟨G'.map (s45_Psi (m : ℝ) e).symm, hGprob, s99_gauss_back m e hG'', ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨F.K * ∑' j, cbNorm (J1 d) (φ j), fun x => ?_⟩
    rw [hell x, LinearIsometryEquiv.norm_map]
    exact s99_ellv_norm hd hs0 hs ha hβ hγ hT hφ F x
  · intro α
    simp_rw [hell, s99_coord_symm, s99_ellv_coord hd hs0 hs ha hβ hγ hT hφ F]
    exact (s99_ua hd hs0 hs ha hβ hγ hT hφ F (e.symm α)).1.continuous
  · have hcont : Continuous fun x => r2EllPt (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) γ m x := by
      have : (fun x => r2EllPt (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) γ m x) =
          fun x => (s45_Psi (m : ℝ) e).symm (ellv d s a β γ φ x) := funext hell
      rw [this]; exact (s45_Psi (m : ℝ) e).symm.continuous.comp hellc
    exact s99_tensor_of_cont (thermalMeasure d s a β) hcont (C := F.K * ∑' j, cbNorm (J1 d) (φ j)) (fun x => by
      rw [hell x, LinearIsometryEquiv.norm_map]
      exact s99_ellv_norm hd hs0 hs ha hβ hγ hT hφ F x)
  · intro N hN2
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN2).prob
    haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
    have hPe : modulatedGibbs (rieszKernel d s) N γ (withDensityReal (thermalDensity d s a β)) =
        S46.s46_P d s a β γ N := (s99_P_eq hd hs0 hs ha hβ hγ N).symm
    rw [hPe]
    have hz : (zetaB (m : ℝ) (S46.s46_P d s a β γ N) : EucConfig d N → OscDual d (m : ℝ)) =
        fun X => (s45_Psi (m : ℝ) e).symm (featureVec φ (S46.s46_nu d s a β γ N) X) := by
      funext X
      have := s45_Psi_zetaB hmd e hφ (S46.s46_P d s a β γ N) (hS N hN2).exch hN1 X
      rw [← this]; simp
    rw [hz]
    exact (s45_Psi (m : ℝ) e).symm.continuous.measurable.comp
      (s99_W_contDiff hN1 (by unfold J1; omega) hφ).continuous.measurable
  · intro ε hε
    obtain ⟨N0, hN0⟩ := s99_main_l2 hd hs0 hs ha hβ hγ hT hS hφ F hG' ε hε
    refine ⟨N0, fun N hN hN2 Φ hΦ => ?_⟩
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN2).prob
    haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
    have hPe : modulatedGibbs (rieszKernel d s) N γ (withDensityReal (thermalDensity d s a β)) =
        S46.s46_P d s a β γ N := (s99_P_eq hd hs0 hs ha hβ hγ N).symm
    rw [hPe]
    have hz : (zetaB (m : ℝ) (S46.s46_P d s a β γ N) : EucConfig d N → OscDual d (m : ℝ)) =
        fun X => (s45_Psi (m : ℝ) e).symm (featureVec φ (S46.s46_nu d s a β γ N) X) := by
      funext X
      have := s45_Psi_zetaB hmd e hφ (S46.s46_P d s a β γ N) (hS N hN2).exch hN1 X
      rw [← this]; simp
    set Ψs := s45_Psi (m : ℝ) e with hΨs
    set Φ' : SeqL2 → ℝ := fun z => Φ (Ψs.symm z) with hΦ'
    have hb : ∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ' z‖ ≤ 1 := fun i hi z => by
      have := Ψs.symm.norm_iteratedFDeriv_comp_right Φ z i
      have h2 : ‖iteratedFDeriv ℝ i Φ' z‖ = ‖iteratedFDeriv ℝ i Φ (Ψs.symm z)‖ := this
      rw [h2]; exact s99_ball_bd hΦ i hi _
    have hΦc : ContDiff ℝ 5 Φ' := hΦ.1.comp Ψs.symm.contDiff
    have main := hN0 N hN hN2 hΦc hb
    have e1 : ∫ X, Φ ((zetaB (m : ℝ) (S46.s46_P d s a β γ N)) X) ∂(S46.s46_P d s a β γ N) =
        ∫ X, Φ' (featureVec φ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
      rw [hz]
    have e2 : ∫ F, Φ F ∂(G'.map Ψs.symm) = ∫ z, Φ' z ∂G' :=
      Ψs.symm.toHomeomorph.measurableEmbedding.integral_map Φ
    have hthird : ∀ (z ℓ : SeqL2), iteratedFDeriv ℝ 3 Φ' z ![ℓ, ℓ, ℓ] =
        iteratedFDeriv ℝ 3 Φ (Ψs.symm z) ![Ψs.symm ℓ, Ψs.symm ℓ, Ψs.symm ℓ] := by
      intro z ℓ
      have := ContinuousLinearMap.iteratedFDeriv_comp_right
        (Ψs.symm.toContinuousLinearEquiv.toContinuousLinearMap) hΦ.1 z (show 3 ≤ 5 by norm_num)
      have h2 : iteratedFDeriv ℝ 3 Φ' z = (iteratedFDeriv ℝ 3 Φ (Ψs.symm z)).compContinuousLinearMap
          fun _ => Ψs.symm.toContinuousLinearEquiv.toContinuousLinearMap := this
      rw [h2, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1
      ext i; fin_cases i <;> rfl
    have e3 : ∫ F, (∫ x, iteratedFDeriv ℝ 3 Φ F ![r2EllPt (rieszKernel d s)
          (withDensityReal (thermalDensity d s a β)) γ m x, r2EllPt (rieszKernel d s)
          (withDensityReal (thermalDensity d s a β)) γ m x, r2EllPt (rieszKernel d s)
          (withDensityReal (thermalDensity d s a β)) γ m x] ∂(withDensityReal (thermalDensity d s a β)))
        ∂(G'.map Ψs.symm) = ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ' z ![ellv d s a β γ φ x, ellv d s a β γ φ x,
          ellv d s a β γ φ x] ∂(thermalMeasure d s a β) ∂G' := by
      refine Eq.trans (Ψs.symm.toHomeomorph.measurableEmbedding.integral_map (μ := G') _) ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hell, hthird]
      rfl
    rw [e1, e2, e3]
    exact main

end S99

end
