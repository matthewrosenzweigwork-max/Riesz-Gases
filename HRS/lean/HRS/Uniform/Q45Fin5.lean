import HRS.Uniform.Q45Fin4

/-!
# Q45: finite-dimensional comparison (assembly)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **Finite-dimensional comparison.**  For the block sums `ζ_j = ∑_k ⟨α_{j,k}, ΔM_k⟩` of two Hilbert martingales (the second
with deterministic covariance density `Cb`), a bounded linear map `L` with `‖L‖ ≤ 1` into a normed space and an `ℱ₀`-measurable
shift `ξ`, the laws of `L(ξ + ζ^M)` and `L(ξ + ζ^G)` differ in `C_b²` by at most `½ K² E∫‖Σ - Cb‖_{𝔖₁}`, where
`K` bounds `‖L(⟨α_{·,k}, x⟩)‖ ≤ K‖x‖` (blockwise). -/
theorem finite_comparison {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ℱ : Filtration ℝ mΩ} {T : ℝ} (hT : 0 < T) {Nb : ℕ} (hNb : 1 ≤ Nb)
    {m : ℕ} (α : Fin m → ℕ → H) (L : (ℝ^m) →L[ℝ] W) (hL : ‖L‖ ≤ 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ k < Nb, ∀ x : H, ‖L (WithLp.toLp 2 (fun j => inner ℝ (α j k) x))‖ ≤ K * ‖x‖)
    {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
    (ξ : Ω → ℝ^m) (hξ : StronglyMeasurable[ℱ 0] ξ) {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) :
    |∫ ω, Φ (L (ξ ω + zeta α T Nb M ω)) ∂P - ∫ ω, Φ (L (ξ ω + zeta α T Nb G ω)) ∂P| ≤
      (1 / 2) * K ^ 2 * covDiscrepancy P T Sg Cb := by
  obtain ⟨q, fH, A, hfH, hA0, hspan, hAu⟩ := exists_block_data Nb α
  set c2 : ℝ := ∑ k ∈ Finset.range Nb, ∑ j, ∑ c, A k j c ^ 2 with hc2
  have hc2n : 0 ≤ c2 := by positivity
  set c : ℝ := Real.sqrt c2 with hcdef
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hdot : ∀ u : Fin q → ℝ, 0 ≤ u ⬝ᵥ u := fun u =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hA : ∀ k (u : Fin q → ℝ), ((A k).mulVec u) ⬝ᵥ ((A k).mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u) := by
    intro k u
    by_cases hk : k < Nb
    · refine (mulVec_sq_le_frob (A k) u).trans ?_
      rw [hcdef, Real.sq_sqrt hc2n]
      refine mul_le_mul_of_nonneg_right ?_ (hdot u)
      exact Finset.single_le_sum (f := fun k => ∑ j, ∑ c, A k j c ^ 2)
        (fun _ _ => by positivity) (Finset.mem_range.2 hk)
    · rw [hA0 k (not_lt.1 hk)]
      simp only [Matrix.zero_mulVec, dotProduct_zero]
      exact mul_nonneg (sq_nonneg c) (hdot u)
  have hN := isVectorMartingale_coord P hM hfH
  have hN' := isVectorMartingale_coord P hG hfH
  have hρ0 := rhoL_nonneg L
  have hρc := rhoL_le hL
  have hν := pairNorm_nu hρ0 hρc zero_le_one
  have hΦL : (Φ ∘ L) ∈ CbUnitBall (ℝ^m) 2 := cbUnitBall_comp_clm L hL hΦ
  obtain ⟨hh, hB0, hG1, hH2⟩ := cbUnit_bounds hΦL
  have key := blocks_comparison P hT hNb hc0 hA hN hN' ξ hξ (Φ ∘ L) hh 1 1 1 1 zero_le_one hH2 hB0
    hG1 hν (hpair_L hL hΦ)
  have hz : ∀ (M' : ℝ → Ω → H) (ω : Ω), blockProc A Nb T (fun τ ω => hmCoordCLM fH (M' τ ω)) T ω =
      zeta α T Nb M' ω := fun M' ω => zeta_eq_blockProc hT α fH A hspan M' ω
  simp only [Function.comp, hz] at key
  -- the pointwise bound on the pairing seminorm
  have hAρ : ∀ k (u : Fin q → ℝ), rhoL L ((A k).mulVec u) ≤ K * Real.sqrt (u ⬝ᵥ u) := by
    intro k u
    by_cases hk : k < Nb
    · have h1 : ‖∑ c, u c • fH c‖ = Real.sqrt (u ⬝ᵥ u) := by
        have := norm_embedCLM_apply hfH (WithLp.toLp 2 u)
        rw [embedCLM_apply] at this
        rw [show ∑ c, u c • fH c = ∑ c, (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin q)) c • fH c from rfl,
          this, EuclideanSpace.norm_eq]
        simp [dotProduct, sq]
      have h2 : (A k).mulVec u = fun j => inner ℝ (α j k) (∑ c, u c • fH c) := by
        funext j; exact hAu k hk j u
      unfold rhoL
      rw [h2, ← h1]
      exact hK k hk _
    · rw [hA0 k (not_lt.1 hk)]
      simp [rhoL]
      positivity
  have hpt : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      nuRho (rhoL L) (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ) ≤
        K ^ 2 * traceNormForm (Sg σ ω - Cb σ) := by
    filter_upwards [hM.sigma_traceClass] with ω htc σ hσ
    have e1 : blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ =
        blockCov A Nb T (compMat fH (Sg σ ω - Cb σ)) σ := by
      have : compMat fH (Sg σ ω - Cb σ) = compMat fH (Sg σ ω) - compMat fH (Cb σ) := by
        ext a b; simp [compMat]
      rw [this]
      simp [blockCov, Matrix.mul_sub, Matrix.sub_mul]
    rw [e1]
    unfold blockCov
    refine (nu_conj_le hρ0 (A (blk Nb T σ)) hK0 (hAρ _) _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
    exact traceNormMatrix_compMat_le hfH (bddAbove_pairSum_sub (htc σ hσ) (hCb.traceClass σ hσ))
  have hint1 := discrepancy_pathint P hM hCb
  have hint2 := discrepancy_integrable P hM hCb
  have hν_int : ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, nuRho (rhoL L)
      (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ)) ∂P ≤
      K ^ 2 * covDiscrepancy P T Sg Cb := by
    unfold covDiscrepancy
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω =>
      setIntegral_nonneg measurableSet_Icc fun σ _ => hν.nonneg _) (hint2.const_mul _) ?_
    filter_upwards [hpt, hint1] with ω hω hω1
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun σ => hν.nonneg _) (hω1.1.const_mul _) ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ hσ => hω σ hσ)
  calc _ ≤ (1 / 2) * 1 * ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, nuRho (rhoL L)
        (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ)) ∂P := key
    _ ≤ (1 / 2) * 1 * (K ^ 2 * covDiscrepancy P T Sg Cb) := by gcongr
    _ = _ := by ring

end HRS.Uniform.Q45
