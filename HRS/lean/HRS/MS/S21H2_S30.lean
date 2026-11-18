import HRS.MS.S21H2_S30C

/-!
# S21H2, packet R26-T3.S30 (repaired): independent initial feature expansion at `γ = 0`

The Pro contract `r26t3_static_iid` claims a `C/√N` rate over the whole `C_b^5` unit ball of `ℓ²`; the merged iid
Edgeworth theorem (`hilbert_edgeworth_C4`, through `s11iid_core`) gives only the qualitative `∀ ε ∃ N₀ ∀ N ≥ N₀` form.
`r26t3_static_iid_qual` is that qualitative form (same `G`, `K`, same expansion; the `C/√N` conjunct is replaced
by `∀ ε > 0 ∃ N₀ ∀ N ≥ N₀`), proved from `s11iid_core` applied to the centered feature `Y` of part A.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem r26t3_static_iid_qual {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : p.γ = 0) (q : ℕ → Euc p.d → ℝ)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) q) :
    ∃ (G : Measure SeqL2) (K : projTensor SeqL2 3),
      IsProbabilityMeasure G ∧
      IsCenteredGaussianSeq G (fun j k => HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (r26t3_mu R 0) 0 (q j) (q k)) ∧
      (K : TensorDual SeqL2 3) = HRS.MS.S21E.s21eKappa0 (r26t3_mu R 0) (r26t3_ell R q) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → 2 ≤ N → ∀ Φ : SeqL2 → ℝ,
        Φ ∈ CbUnitBall SeqL2 5 →
        |Real.sqrt N * ((∫ X, Φ (r26t3_W R q N X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
          (1 / 6) * (∫ z, (K : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Φ z) ∂G)| ≤ ε := by
  have hdens := (r26t3_reference_data p δ hδ hδh R).2.2.1 0 le_rfl
  have hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s11iid_prob hdens.1.nonneg hdens.1.integral_one
  set μ := r26t3_mu R 0 with hμdef
  obtain ⟨G, hGp, hGg, hGcov⟩ := s21h2_exists_gaussian hq μ
  obtain ⟨K, hKeq, hKapp⟩ := s21h2_tensor hq μ
  have hell : r26t3_ell R q = s21h2_Y q μ := by
    funext x
    unfold r26t3_ell r26t3_a s21h2_Y
    congr 1
    funext j
    simp [HRS.Whole.responseRepW, hγ, HRS.Whole.projMean, hμdef]
  obtain ⟨C, hC⟩ := s21h2_norm_le hq μ
  have hw : Summable fun j => (2 * cbNorm (r26t3_J p.d) (q j)) ^ 2 := s21h2_summable_sq hq
  have hcore := s11iid_core μ S45.s45_seqBasis (s21h2_Y q μ) (s21h2_continuous hq μ) C hC
    (s21h2_centered hq μ) _ hw
    (fun n x => by
      rw [s21h2_inner hq μ]
      have := s21h2_abs_le hq μ x n
      exact (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) this 2)) G hGg hGcov
  refine ⟨G, K, hGp, s21h2_gauss_seq hq μ _ G hGg hGcov, by rw [hKeq, hell], fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hcore ε hε
  refine ⟨N₀, fun N hN hN2 Φ hΦ => ?_⟩
  have h := hN₀ N hN (by omega) Φ hΦ
  have hQ : r26t3_Q R N = Measure.pi fun _ : Fin N => μ := by
    unfold r26t3_Q
    rw [hγ]
    exact s11iid_gibbs_zero _ N μ
  have hWf : r26t3_W R q N = HRS.StaticLimitAux.Ssum (s21h2_Y q μ) N := by
    funext X
    unfold r26t3_W r26t3_marg
    rw [hQ, s21h2_marg_pi N (by omega) μ]
    exact s21h2_W_eq hq μ N (by omega) X
  rw [hQ, hWf]
  have hinner : ∫ z, (K : TensorDual SeqL2 3) (iteratedFDeriv ℝ 3 Φ z) ∂G =
      ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![s21h2_Y q μ x, s21h2_Y q μ x, s21h2_Y q μ x] ∂μ ∂G :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => hKapp _)
  rw [hinner]
  exact h

end HRS.MS.R26T3
