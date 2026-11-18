import HRS.MS.QsfOsc7

/-!
# S4.5: proof of `quadratic_static_field_osc`
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

theorem s45_unit_ball_bounds' {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ}
    (hΦ : Φ ∈ HRS.CbUnitBall B 2) :
    (∀ z, ‖fderiv ℝ Φ z‖ ≤ 1) ∧ (∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ 1) := by
  obtain ⟨-, hbdd, hcb⟩ := hΦ
  have hnn : ∀ j, 0 ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ := fun j =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have hle : ∀ j ∈ Finset.range 3, ∀ z : B, ‖iteratedFDeriv ℝ j Φ z‖ ≤ 1 := by
    intro j hj z
    have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ :=
      le_ciSup (hbdd j (by simpa [Nat.lt_succ_iff] using hj)) z
    have h2 : ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ ≤ HRS.cbNorm 2 Φ := by
      unfold HRS.cbNorm
      exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
        (fun j _ => hnn j) hj
    linarith
  refine ⟨fun z => ?_, fun z => hle 2 (by simp) z⟩
  rw [← norm_iteratedFDeriv_one]
  exact hle 1 (by simp) z

theorem quadratic_static_field_osc_proof : type_of% @HRS.Whole.quadratic_static_field_osc := by
  intro d s hd hs0 hsd a β ha hβ J hJ m hm
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C1, hC1⟩ := quadratic_static_field_proof hd hs0 hsd a β ha hβ J hJ
  obtain ⟨Cs, -, hS⟩ := s45_static_all hd hs0 hsd ha hβ
  obtain ⟨Ct, ct, BU, hT⟩ := s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨e⟩ := s45_exists_enum hd1
  have hJ1 : 1 ≤ J := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have h1 : (1 : ℝ) ≤ J := by linarith
    exact_mod_cast h1
  have hmd : (d : ℝ) < m := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    linarith
  have hφ : HRS.Whole.IsSummableFeatureFamily J (fun j : ℕ => oscTestFun m (e j)) :=
    s45_summable_oscTest hd1 J hm e
  set S := featureSum J (fun j : ℕ => oscTestFun m (e j)) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun i => HRS.MS.Tc5.tc5_cb_nonneg J _
  refine ⟨max C1 0 * (S + S ^ 2), ?_⟩
  intro N hN γ hγ
  have hN1 : 1 ≤ N := by omega
  have hSN := hS N hN
  haveI hP : IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β) := hSN.prob
  set P := canonicalGibbs (rieszKernel d s) (confinement a) N β with hPdef
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  -- the Gaussian on `ℓ²`
  have hmem : ∀ α : MultiIndex d, MemLp (hermiteFunD α) 2 (thermalMeasure d s a β) := by
    intro α
    obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
    exact MemLp.of_bound (contDiff_hermiteFunD α).continuous.aestronglyMeasurable C0
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC0 α x)
  have hγ' : IsCenteredGaussianSeq (γ.map (s45_Psi m e)) fun i j => susceptibilityCov
      (rieszKernel d s) (thermalMeasure d s a β) β (oscTestFun m (e i)) (oscTestFun m (e j)) := by
    have h := s45_gauss_transport e hγ
    convert h using 3 with i j
    have := s45_cov_smul hd hs0 hsd hβ hT (hmem (e i)) (hmem (e j))
      (oscEigenvalue d (e i) ^ (-(m / 2))) (oscEigenvalue d (e j) ^ (-(m / 2)))
    exact this
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hC1 (fun j : ℕ => oscTestFun m (e j)) hφ N hN (γ.map (s45_Psi m e)) hγ'
  have hzeta : ∀ X : EucConfig d N, zetaB m P X =
      (s45_Psi m e).symm (featureVec (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X) := by
    intro X
    rw [← s45_Psi_zetaB hmd e hφ P hSN.exch hN1 X]
    simp
  have hmeas : Measurable (zetaB m P : EucConfig d N → OscDual d m) := by
    have : (zetaB m P : EucConfig d N → OscDual d m) = fun X => (s45_Psi m e).symm
        (featureVec (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X) := funext hzeta
    rw [this]
    exact (s45_Psi m e).symm.continuous.measurable.comp hk2
  refine ⟨hmeas, ?_⟩
  unfold HRS.smoothDist
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ1, hΦ2⟩ := s45_unit_ball_bounds' Φ.2
  have hΦc : ContDiff ℝ 2 Φ.1 := Φ.2.1
  set F : SeqL2 → ℝ := fun z => Φ.1 ((s45_Psi m e).symm z) with hF
  have hFc : ContDiff ℝ 2 F := hΦc.comp (s45_Psi m e).symm.contDiff
  have hD1 : ∀ z, ‖fderiv ℝ F z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]
    have := LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (s45_Psi m e).symm Φ.1 z (i := 1)
    rw [show F = Φ.1 ∘ (s45_Psi m e).symm from rfl, this, norm_iteratedFDeriv_one]
    exact hΦ1 _
  have hD2 : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ 1 := fun z => by
    have := LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (s45_Psi m e).symm Φ.1 z (i := 2)
    rw [show F = Φ.1 ∘ (s45_Psi m e).symm from rfl, this]
    exact hΦ2 _
  obtain ⟨-, -, hbound⟩ := hk4 F hFc 1 1 hD1 hD2
  have e1 : ∫ z, Φ.1 z ∂(HRS.law P (zetaB m P)) = ∫ X, F (featureVec (fun j : ℕ => oscTestFun m (e j))
      (firstMarginal P) X) ∂P := by
    unfold HRS.law
    rw [integral_map hmeas.aemeasurable Φ.2.1.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hzeta, hF]
  have e2 : ∫ z, F z ∂(γ.map (s45_Psi m e)) = ∫ u, Φ.1 u ∂γ := by
    rw [integral_map (s45_Psi m e).continuous.measurable.aemeasurable hFc.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp [hF]
  rw [e1, ← e2]
  refine hbound.trans ?_
  have hδ0 : 0 ≤ Real.sqrt (HRS.deltaN d s N) := Real.sqrt_nonneg _
  have h1 : C1 ≤ max C1 0 := le_max_left _ _
  have h2 : 0 ≤ Real.sqrt (HRS.deltaN d s N) * (S * 1 + S ^ 2 * 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

end S45

end
