import HRS.MS.Fp81S21InitialIid
import HRS.MS.Fp81S21InitialThird
import HRS.Energy.StaticLimitTiltedGauss

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc cbNorm CbUnitBall)
open HRS.MS.R26T3

private theorem fp81s21_initial_iid_gaussian_ext
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

/-- The actual endpoint Edgeworth expansion with a supplied centered Gaussian.
The cutoff is uniform over C⁵ tests whose derivatives of each order zero through five
are bounded by one. -/
theorem fp81s21_initial_main_l2_iid
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j))) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N →
      ∀ {Φ : SeqL2 → ℝ}, ContDiff ℝ 5 Φ →
        (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
        |Real.sqrt N *
            ((∫ X, Φ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
          (1 / 6) * ∫ z, ∫ x,
            iteratedFDeriv ℝ 3 Φ z
              ![fp81s21_initial_ellv R φ x,
                fp81s21_initial_ellv R φ x,
                fp81s21_initial_ellv R φ x]
            ∂(r26t3_mu R 0) ∂G| ≤ ε := by
  haveI hμ : IsProbabilityMeasure (r26t3_mu R 0) := by
    have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
    exact s11iid_prob hdens.1.nonneg hdens.1.integral_one
  obtain ⟨G0, K, hG0p, hG0seq, hKeq, hqual⟩ :=
    HRS.MS.R26T3.r26t3_static_iid_qual hδ hδh R hγ φ hφ
  have hGseq : IsCenteredGaussianSeq G
      (fun i j => HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) 0 (φ i) (φ j)) := by
    simpa [hγ] using hG
  have hGid : G0 = G := fp81s21_initial_iid_gaussian_ext hG0seq hGseq
  intro ε hε
  have hcpos : (0 : ℝ) < 1 / 6 := by norm_num
  obtain ⟨N0, hN0⟩ := hqual (ε / 6) (by linarith)
  refine ⟨N0, fun N hN0N hN2 Φ hΦ hb => ?_⟩
  let c : ℝ := 1 / 6
  let Ψ : SeqL2 → ℝ := fun z => c * Φ z
  have hΨcd : ContDiff ℝ 5 Ψ := by
    have heq : Ψ = c • Φ := by
      funext z
      simp [Ψ]
    rw [heq]
    exact hΦ.const_smul c
  have hΨb : ∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Ψ z‖ ≤ c := by
    intro i hi z
    have heq : Ψ = c • Φ := by
      funext y
      simp [Ψ]
    rw [heq, iteratedFDeriv_const_smul_apply
      (hΦ.of_le (by exact_mod_cast hi)).contDiffAt, norm_smul,
      Real.norm_of_nonneg (by dsimp [c]; positivity)]
    calc
      c * ‖iteratedFDeriv ℝ i Φ z‖ ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (hb i hi z) (by dsimp [c]; positivity)
      _ = c := by ring
  have hΨball : Ψ ∈ CbUnitBall SeqL2 5 := by
    refine ⟨hΨcd, ?_, ?_⟩
    · intro i hi
      refine ⟨c, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hΨb i hi z
    · unfold HRS.cbNorm
      calc
        (∑ i ∈ Finset.range 6, ⨆ z : SeqL2, ‖iteratedFDeriv ℝ i Ψ z‖) ≤
            ∑ i ∈ Finset.range 6, c := by
          apply Finset.sum_le_sum
          intro i hi
          apply ciSup_le
          intro z
          exact hΨb i (Nat.lt_succ_iff.mp (by simpa using hi)) z
        _ = 1 := by norm_num [c]
  have hDΨ : ∀ z, iteratedFDeriv ℝ 3 Ψ z = c • iteratedFDeriv ℝ 3 Φ z := by
    intro z
    have heq : Ψ = c • Φ := by
      funext y
      simp [Ψ]
    rw [heq, iteratedFDeriv_const_smul_apply
      (hΦ.of_le (by exact_mod_cast (show (3 : ℕ) ≤ 5 by norm_num))).contDiffAt]
  let L (F : SeqL2 → ℝ) : ℝ :=
    (∫ X, F (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, F z ∂G
  let T (F : SeqL2 → ℝ) : ℝ :=
    ∫ z, ∫ x, iteratedFDeriv ℝ 3 F z
      ![fp81s21_initial_ellv R φ x,
        fp81s21_initial_ellv R φ x,
        fp81s21_initial_ellv R φ x]
      ∂(r26t3_mu R 0) ∂G
  have hLinScale : L Ψ = c * L Φ := by
    dsimp [L, Ψ]
    rw [integral_const_mul, integral_const_mul]
    ring
  have hCubicScale : T Ψ = c * T Φ := by
    have heval : ∀ z x,
        iteratedFDeriv ℝ 3 Ψ z
            ![fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x] =
          c * iteratedFDeriv ℝ 3 Φ z
            ![fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x] := by
      intro z x
      rw [hDΨ z]
      simp
    dsimp [T]
    calc
      _ = ∫ z, c * (∫ x, iteratedFDeriv ℝ 3 Φ z
            ![fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x]
            ∂(r26t3_mu R 0)) ∂G := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            change (∫ x, iteratedFDeriv ℝ 3 Ψ z
                ![fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x]
                ∂(r26t3_mu R 0)) =
              c * (∫ x, iteratedFDeriv ℝ 3 Φ z
                ![fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x]
                ∂(r26t3_mu R 0))
            rw [← integral_const_mul]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => heval z x
      _ = c * (∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
            ![fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x]
            ∂(r26t3_mu R 0) ∂G) := integral_const_mul c _
  obtain ⟨K', hK'eq, hKapp⟩ := s21h2_tensor hφ (r26t3_mu R 0)
  have hell : ∀ x, fp81s21_initial_ellv R φ x = s21h2_Y φ (r26t3_mu R 0) x := by
    intro x
    unfold fp81s21_initial_ellv s21h2_Y
    congr 1
    funext j
    exact fp81s21_initial_iid_response R hγ (φ j) x
  have hellr : r26t3_ell R φ = s21h2_Y φ (r26t3_mu R 0) := by
    funext x
    exact hell x
  have hcontract : ∀ z,
      (K : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Ψ z) =
        ∫ x, iteratedFDeriv ℝ 3 Ψ z
          ![fp81s21_initial_ellv R φ x,
            fp81s21_initial_ellv R φ x,
            fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0) := by
    intro z
    calc
      (K : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Ψ z) =
          (HRS.MS.S21E.s21eKappa0 (r26t3_mu R 0)
            (r26t3_ell R φ)) (iteratedFDeriv ℝ 3 Ψ z) := by rw [hKeq]
      _ = (HRS.MS.S21E.s21eKappa0 (r26t3_mu R 0)
            (s21h2_Y φ (r26t3_mu R 0))) (iteratedFDeriv ℝ 3 Ψ z) := by
          rw [hellr]
      _ = (K' : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Ψ z) := by rw [hK'eq]
      _ = ∫ x, iteratedFDeriv ℝ 3 Ψ z
            ![s21h2_Y φ (r26t3_mu R 0) x,
              s21h2_Y φ (r26t3_mu R 0) x,
              s21h2_Y φ (r26t3_mu R 0) x] ∂(r26t3_mu R 0) := hKapp _
      _ = ∫ x, iteratedFDeriv ℝ 3 Ψ z
            ![fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x,
              fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change iteratedFDeriv ℝ 3 Ψ z
                ![s21h2_Y φ (r26t3_mu R 0) x,
                  s21h2_Y φ (r26t3_mu R 0) x,
                  s21h2_Y φ (r26t3_mu R 0) x] =
              iteratedFDeriv ℝ 3 Ψ z
                ![fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x,
                  fp81s21_initial_ellv R φ x]
            rw [← hell x]
  have hTensorIntegral :
      ∫ z, (K : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Ψ z) ∂G = T Ψ := by
    dsimp [T]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hcontract
  have hbase := hN0 N hN0N hN2 Ψ hΨball
  rw [hGid, hTensorIntegral] at hbase
  have hbase' : |Real.sqrt N * L Ψ - (1 / 6) * T Ψ| ≤ ε / 6 := by
    simpa [L, r26t3_W] using hbase
  have hscaled : |(1 / 6 : ℝ) * (Real.sqrt N * L Φ - (1 / 6) * T Φ)| ≤ ε / 6 := by
    have hExpr : Real.sqrt N * L Ψ - (1 / 6) * T Ψ =
        (1 / 6 : ℝ) * (Real.sqrt N * L Φ - (1 / 6) * T Φ) := by
      rw [hLinScale, hCubicScale]
      dsimp [c]
      ring
    rw [← hExpr]
    exact hbase'
  have hgoal : |Real.sqrt N * L Φ - (1 / 6) * T Φ| ≤ ε := by
    have habs : (1 / 6 : ℝ) * |Real.sqrt N * L Φ - (1 / 6) * T Φ| ≤ ε / 6 := by
      simpa [abs_mul] using hscaled
    norm_num at habs ⊢
    linarith
  simpa [L, T] using hgoal

#print axioms fp81s21_initial_main_l2_iid

end HRS.Fp81.S21

end
