import HRS.MS.S21F_I00
import HRS.MS.Fp81S21InitialIid2
import HRS.MS.S21H2_S30

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc cbNorm)
open HRS.MS.R26T3

/-- Centered Gaussian probability measures on `SeqL2` with the same coordinate
covariance are equal. -/
theorem fp81s21_initial_iid_gaussian_ext
    {C : ℕ → ℕ → ℝ} {G G' : Measure SeqL2}
    [IsProbabilityMeasure G] [IsProbabilityMeasure G']
    (hG : IsCenteredGaussianSeq G C) (hG' : IsCenteredGaussianSeq G' C) : G = G' := by
  have hdense : Dense (↑(Submodule.span ℝ (Set.range S45.s45_seqBasis)) : Set SeqL2) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 S45.s45_seqBasis.dense_span
  have hcov : ProbabilityTheory.covarianceBilin G = ProbabilityTheory.covarianceBilin G' := by
    refine ContinuousLinearMap.ext_on hdense ?_
    rintro _ ⟨i, rfl⟩
    refine ContinuousLinearMap.ext_on hdense ?_
    rintro _ ⟨j, rfl⟩
    have hg : IsGaussian G := hG.1.1
    have hg' : IsGaussian G' := hG'.1.1
    letI : IsGaussian G := hg
    letI : IsGaussian G' := hg'
    have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
    have hmem' : MemLp id 2 G' := ProbabilityTheory.IsGaussian.memLp_two_id
    have hmean : ∫ z, id z ∂G = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hG.1
    have hmean' : ∫ z, id z ∂G' = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hG'.1
    have h1 : ∫ z, inner ℝ (S45.s45_seqBasis i) z * inner ℝ (S45.s45_seqBasis j) z ∂G =
        ProbabilityTheory.covarianceBilin G (S45.s45_seqBasis i) (S45.s45_seqBasis j) := by
      rw [ProbabilityTheory.covarianceBilin_apply hmem, hmean]
      simp
    have h2 : ∫ z, inner ℝ (S45.s45_seqBasis i) z * inner ℝ (S45.s45_seqBasis j) z ∂G' =
        ProbabilityTheory.covarianceBilin G' (S45.s45_seqBasis i) (S45.s45_seqBasis j) := by
      rw [ProbabilityTheory.covarianceBilin_apply hmem', hmean']
      simp
    rw [← h1, ← h2]
    simpa only [S45.s45_inner_seqBasis] using (hG.2 i j).2.trans ((hG'.2 i j).2.symm)
  exact HRS.StaticLimitAux.gaussian_ext_of_cov G G' hG.1 hG'.1 hcov

/-- At zero coupling, every supplied centered sequence Gaussian with the response
coordinate covariance has the full covariance form of the centered iid feature law.
This is the covariance hypothesis needed by the indexed iid Edgeworth theorem. -/
theorem fp81s21_iid_gaussian_covariance_match
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (a : ℝ) (ha : 0 ≤ a)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a))
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j))) :
    ∀ x y, ProbabilityTheory.covarianceBilin G x y =
      ProbabilityTheory.covarianceBilin
        ((r26t3_mu R 0).map (s21h2_Y (r26t3_qwin R a) (r26t3_mu R 0))) x y := by
  let μ := r26t3_mu R 0
  let q := r26t3_qwin R a
  haveI hμ : IsProbabilityMeasure μ := by
    have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  have hcenter (i j : ℕ) :
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) μ p.γ (q i) (q j) =
        ∫ x, (q i x - HRS.Whole.pair μ (q i)) *
          (q j x - HRS.Whole.pair μ (q j)) ∂μ := by
    exact fp81s21_initial_iid_cov hδ hδh R hγ
      (f := q i) (g := q j) (hq.1 j).1.continuous
      (Cg := cbNorm (r26t3_J p.d) (q j)) (fun x => by
        have hx := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) x
        rwa [Real.norm_eq_abs] at hx)
  have hGc : IsCenteredGaussianSeq G (fun i j =>
      ∫ x, (q i x - HRS.Whole.pair μ (q i)) *
        (q j x - HRS.Whole.pair μ (q j)) ∂μ) := by
    rcases hG with ⟨hGauss, hcoords⟩
    refine ⟨hGauss, ?_⟩
    intro i j
    rcases hcoords i j with ⟨hint, hval⟩
    exact ⟨hint, hval.trans (hcenter i j)⟩
  obtain ⟨G₀, hG₀prob, hG₀gauss, hG₀cov⟩ := s21h2_exists_gaussian hq μ
  letI : IsProbabilityMeasure G₀ := hG₀prob
  have hG₀seq := s21h2_gauss_seq hq μ (HRS.Whole.rieszKernel p.d p.s)
    G₀ hG₀gauss hG₀cov
  have hG₀c : IsCenteredGaussianSeq G₀ (fun i j =>
      ∫ x, (q i x - HRS.Whole.pair μ (q i)) *
        (q j x - HRS.Whole.pair μ (q j)) ∂μ) := by
    rcases hG₀seq with ⟨hGauss, hcoords⟩
    refine ⟨hGauss, ?_⟩
    intro i j
    rcases hcoords i j with ⟨hint, hval⟩
    exact ⟨hint, hval.trans (HRS.MS.R26T3.s21h2_susc hq μ
      (HRS.Whole.rieszKernel p.d p.s) i j)⟩
  have hGid : G = G₀ := fp81s21_initial_iid_gaussian_ext hGc hG₀c
  intro x y
  rw [hGid]
  exact hG₀cov x y

#print axioms fp81s21_initial_iid_gaussian_ext
#print axioms fp81s21_iid_gaussian_covariance_match

end HRS.Fp81.S21

end
