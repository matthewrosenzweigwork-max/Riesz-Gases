import HRS.MS.R2ObsAux2

/-!
# S9.10 family row: proof of `HRS.Whole.r2_static_observation_family`

Worker S910.  `r2_static_observation_family_proof : type_of% @HRS.Whole.r2_static_observation_family` (tie in `R2ObsTie.lean`).
The proof is the proof of `round2_static_edgeworth_proof` (R2SeAux49) with the isometry `Ψ = e.repr : H ≃ₗᵢ ℓ²(ℕ)` of the given
orthonormal basis in place of `s45_Psi`: the `ℓ²` Edgeworth expansion `s99_main_l2` for the features `ψ_j` is pulled back to `H`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS HRS.Whole
open HRS (Euc cbNorm MemCb)

universe u

set_option maxHeartbeats 4000000 in
theorem r2_static_observation_family_proof.{v} : type_of% @HRS.Whole.r2_static_observation_family.{v} := by
  intro d s H _ _ _ _ _ _ hd hs0 hs a β γ ha hβ hγ e ψ hψ hsum ρ hρ
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hd1 : 1 ≤ d := by omega
  have hρeq := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  have hφ : IsSummableFeatureFamily (J1 d) ψ := ⟨hψ, hsum⟩
  obtain ⟨E⟩ := s910_env hd hs0 hs ha hβ hγ hφ
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.hT.prob
  obtain ⟨L, hL⟩ := s45_thermal_logmoment2 E.hT
  have hM : ∀ x, thermalDensity d s a β x ≤ E.C := fun x => (le_abs_self _).trans
    ((E.hT.h0 x).trans (by
      have : Real.exp (-E.c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, E.hT.hc])
      nlinarith [E.hT.C0]))
  obtain ⟨-, G', hG'⟩ := exists_gaussian_feature_proof hd hs0 hsd (J1 d) (J1_gt d) (thermalDensity d s a β)
    E.hT.prob E.C hM γ hγ ψ hφ L (fun _ => hL)
  haveI hGG : ProbabilityTheory.IsGaussian G' := hG'.1.1
  have hΨm : Measurable (s910_Psi e).symm := (s910_Psi e).symm.continuous.measurable
  haveI hGprob : IsProbabilityMeasure (G'.map (s910_Psi e).symm) :=
    ⟨by rw [Measure.map_apply hΨm MeasurableSet.univ]; simp⟩
  have hell : ∀ x, r2EllH e ψ (rieszKernel d s) (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x =
      (s910_Psi e).symm (ellv d s a β γ ψ x) := s910_ell_eq hd hs0 hs ha hβ hγ E e
  refine ⟨G'.map (s910_Psi e).symm, hGprob, s910_gauss_symm e hG'.1, fun j k => s910_cov_map e hG' j k,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨E.F.K * ∑' j, cbNorm (J1 d) (ψ j), fun x => s910_ell_norm hd hs0 hs ha hβ hγ E e x⟩
  · exact s910_tensor (thermalMeasure d s a β) _ (s910_ell_cont hd hs0 hs ha hβ hγ E e)
      (Cb := E.F.K * ∑' j, cbNorm (J1 d) (ψ j)) (fun x => s910_ell_norm hd hs0 hs ha hβ hγ E e x)
  · intro N hN2
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (E.hS N hN2).prob
    haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
    have hPe : HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β)) =
        S46.s46_P d s a β γ N := (s99_P_eq hd hs0 hs ha hβ hγ N).symm
    rw [hPe]
    have hz : (r2FieldH e ψ (S46.s46_P d s a β γ N) : EucConfig d N → H) =
        fun X => (s910_Psi e).symm (featureVec ψ (S46.s46_nu d s a β γ N) X) := funext fun X =>
      s910_field_eq hN1 e hφ (S46.s46_P d s a β γ N) (E.hS N hN2).exch X
    rw [hz]
    exact (s910_Psi e).symm.continuous.measurable.comp
      (s99_W_contDiff hN1 (by unfold J1; omega) hφ).continuous.measurable
  · intro ε hε
    obtain ⟨N0, hN0⟩ := s99_main_l2 hd hs0 hs ha hβ hγ E.hT E.hS hφ E.F hG' ε hε
    refine ⟨N0, fun N hN hN2 Φ hΦ => ?_⟩
    have hN1 : 1 ≤ N := by omega
    haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (E.hS N hN2).prob
    haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob hN1
    have hPe : HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal (thermalDensity d s a β)) =
        S46.s46_P d s a β γ N := (s99_P_eq hd hs0 hs ha hβ hγ N).symm
    rw [hPe]
    have hz : (r2FieldH e ψ (S46.s46_P d s a β γ N) : EucConfig d N → H) =
        fun X => (s910_Psi e).symm (featureVec ψ (S46.s46_nu d s a β γ N) X) := funext fun X =>
      s910_field_eq hN1 e hφ (S46.s46_P d s a β γ N) (E.hS N hN2).exch X
    set Ψs := s910_Psi e with hΨs
    set Φ' : SeqL2 → ℝ := fun z => Φ (Ψs.symm z) with hΦ'
    have hb : ∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ' z‖ ≤ 1 := fun i hi z => by
      have := Ψs.symm.norm_iteratedFDeriv_comp_right Φ z i
      have h2 : ‖iteratedFDeriv ℝ i Φ' z‖ = ‖iteratedFDeriv ℝ i Φ (Ψs.symm z)‖ := this
      rw [h2]; exact s99_ball_bd hΦ i hi _
    have hΦc : ContDiff ℝ 5 Φ' := hΦ.1.comp Ψs.symm.contDiff
    have main := hN0 N hN hN2 hΦc hb
    have e1 : ∫ X, Φ (r2FieldH e ψ (S46.s46_P d s a β γ N) X) ∂(S46.s46_P d s a β γ N) =
        ∫ X, Φ' (featureVec ψ (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) := by
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
    have e3 : ∫ F, (∫ x, iteratedFDeriv ℝ 3 Φ F ![r2EllH e ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x, r2EllH e ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x, r2EllH e ψ (rieszKernel d s)
          (HRS.Whole.withDensityReal (thermalDensity d s a β)) γ x] ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)))
        ∂(G'.map Ψs.symm) = ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ' z ![ellv d s a β γ ψ x, ellv d s a β γ ψ x,
          ellv d s a β γ ψ x] ∂(thermalMeasure d s a β) ∂G' := by
      refine Eq.trans (Ψs.symm.toHomeomorph.measurableEmbedding.integral_map (μ := G') _) ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hell, hthird]
      rfl
    rw [e1, e2, e3]
    exact main

end HRS.MS.R2Obs

end
