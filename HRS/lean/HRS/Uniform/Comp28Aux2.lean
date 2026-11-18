import HRS.Uniform.Comp28Aux1

/-!
# COMP-28, part 2: the finite-dimensional comparison with a block-dependent constant

`finite_comparison_w` is `Q45.finite_comparison` with the single constant `K` replaced by `Kf k` on the `k`-th block; the
conclusion is `½ E∫ Kf(blk σ)² ‖Σ - Cb‖_{𝔖₁}` (`blk Nb T σ` is the block index of `σ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

section Weighted

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)}

/-- The weighted trace-norm discrepancy `E ∫_0^t ϖ(σ) ‖Σ_σ - Σ̄_σ‖_{𝔖₁} dσ`. -/
def covDiscW (t : ℝ) (ϖ : ℝ → ℝ) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) : ℝ :=
  ∫ ω, (∫ σ in Set.Icc 0 t, ϖ σ * traceNormForm (Sg σ ω - sb σ)) ∂P

lemma wdisc_pathint (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (hsb : IsDetCovDensity t sb)
    {ϖ : ℝ → ℝ} (hϖm : Measurable ϖ) (hϖ0 : ∀ σ, 0 ≤ ϖ σ) {B : ℝ} (hϖB : ∀ σ, ϖ σ ≤ B) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => ϖ σ * traceNormForm (Sg σ ω - sb σ)) (Set.Icc 0 t) := by
  have hmeas := measurable_discrepancy_density P hM hsb
  filter_upwards [discrepancy_pathint P hM hsb] with ω hω
  refine Integrable.mono' (hω.1.const_mul B)
    ((hϖm.mul (hmeas.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hϖ0 σ) (traceNormForm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hϖB σ) (traceNormForm_nonneg _)

lemma wdisc_integrable (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg) (hsb : IsDetCovDensity t sb)
    {ϖ : ℝ → ℝ} (hϖm : Measurable ϖ) (hϖ0 : ∀ σ, 0 ≤ ϖ σ) {B : ℝ} (hϖB : ∀ σ, ϖ σ ≤ B) :
    Integrable (fun ω => ∫ σ in Set.Icc 0 t, ϖ σ * traceNormForm (Sg σ ω - sb σ)) P := by
  have hmeas := measurable_discrepancy_density P hM hsb
  have hjm := hmeas.comp (measurable_swap (α := Ω) (β := ℝ))
  have hj := (hϖm.comp (measurable_snd (α := Ω) (β := ℝ))).mul hjm
  have hsm : StronglyMeasurable fun ω => ∫ σ in Set.Icc 0 t, ϖ σ * traceNormForm (Sg σ ω - sb σ) :=
    hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc 0 t))
  refine Integrable.mono' ((discrepancy_integrable P hM hsb).const_mul B) hsm.aestronglyMeasurable ?_
  filter_upwards [discrepancy_pathint P hM hsb, wdisc_pathint P hM hsb hϖm hϖ0 hϖB] with ω hd hw
  rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ =>
    mul_nonneg (hϖ0 σ) (traceNormForm_nonneg _))]
  rw [← integral_const_mul]
  refine setIntegral_mono_on hw (hd.1.const_mul B) measurableSet_Icc fun σ _ => ?_
  exact mul_le_mul_of_nonneg_right (hϖB σ) (traceNormForm_nonneg _)

end Weighted

/-- **Finite-dimensional comparison, blockwise constants.**  As `Q45.finite_comparison`, with `‖L(⟨α_{·,k}, x⟩)‖ ≤ Kf k ‖x‖`
on the `k`-th block, the bound is `½ E∫ Kf(blk σ)² ‖Σ - Cb‖_{𝔖₁}`. -/
theorem finite_comparison_w {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ℱ : Filtration ℝ mΩ} {T : ℝ} (hT : 0 < T) {Nb : ℕ} (hNb : 1 ≤ Nb)
    {m : ℕ} (α : Fin m → ℕ → H) (L : (ℝ^m) →L[ℝ] W) (hL : ‖L‖ ≤ 1) (Kf : ℕ → ℝ) (hK0 : ∀ k, 0 ≤ Kf k)
    (hK : ∀ k < Nb, ∀ x : H, ‖L (WithLp.toLp 2 (fun j => inner ℝ (α j k) x))‖ ≤ Kf k * ‖x‖)
    {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {G : ℝ → Ω → H} {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
    (ξ : Ω → ℝ^m) (hξ : StronglyMeasurable[ℱ 0] ξ) {Φ : W → ℝ} (hΦ : Φ ∈ CbUnitBall W 2) :
    |∫ ω, Φ (L (ξ ω + zeta α T Nb M ω)) ∂P - ∫ ω, Φ (L (ξ ω + zeta α T Nb G ω)) ∂P| ≤
      (1 / 2) * ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, Kf (blk Nb T σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ)) ∂P := by
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
  -- the pointwise bound on the pairing seminorm, blockwise
  have hAρ : ∀ k (u : Fin q → ℝ), rhoL L ((A k).mulVec u) ≤ Kf k * Real.sqrt (u ⬝ᵥ u) := by
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
      exact mul_nonneg (hK0 k) (Real.sqrt_nonneg _)
  have hpt : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      nuRho (rhoL L) (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ) ≤
        Kf (blk Nb T σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ) := by
    filter_upwards [hM.sigma_traceClass] with ω htc σ hσ
    have e1 : blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ =
        blockCov A Nb T (compMat fH (Sg σ ω - Cb σ)) σ := by
      have : compMat fH (Sg σ ω - Cb σ) = compMat fH (Sg σ ω) - compMat fH (Cb σ) := by
        ext a b; simp [compMat]
      rw [this]
      simp [blockCov, Matrix.mul_sub, Matrix.sub_mul]
    rw [e1]
    unfold blockCov
    refine (nu_conj_le hρ0 (A (blk Nb T σ)) (hK0 _) (hAρ _) _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact traceNormMatrix_compMat_le hfH (bddAbove_pairSum_sub (htc σ hσ) (hCb.traceClass σ hσ))
  -- the weight `σ ↦ Kf(blk σ)²` is measurable and bounded
  set Kmax : ℝ := ∑ k ∈ Finset.range Nb, Kf k ^ 2 with hKmax
  have hϖm : Measurable fun σ : ℝ => Kf (blk Nb T σ) ^ 2 :=
    ((measurable_from_top (f := fun k : ℕ => Kf k ^ 2)).comp (measurable_blk Nb T))
  have hϖ0 : ∀ σ : ℝ, 0 ≤ Kf (blk Nb T σ) ^ 2 := fun σ => sq_nonneg _
  have hϖB : ∀ σ : ℝ, Kf (blk Nb T σ) ^ 2 ≤ Kmax := by
    intro σ
    have hb : blk Nb T σ < Nb := by
      unfold blk
      exact lt_of_le_of_lt (min_le_right _ _) (by omega)
    exact Finset.single_le_sum (f := fun k => Kf k ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_range.2 hb)
  have hint1 := discrepancy_pathint P hM hCb
  have hint2 := discrepancy_integrable P hM hCb
  have hw1 := wdisc_pathint P hM hCb hϖm hϖ0 hϖB
  have hw2 := wdisc_integrable P hM hCb hϖm hϖ0 hϖB
  have hν_int : ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, nuRho (rhoL L)
      (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ)) ∂P ≤
      ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, Kf (blk Nb T σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ)) ∂P := by
    refine integral_mono_of_nonneg (ae_of_all _ fun ω =>
      setIntegral_nonneg measurableSet_Icc fun σ _ => hν.nonneg _) hw2 ?_
    filter_upwards [hpt, hw1] with ω hω hω1
    refine integral_mono_of_nonneg (ae_of_all _ fun σ => hν.nonneg _) hω1 ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ hσ => hω σ hσ)
  calc _ ≤ (1 / 2) * 1 * ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T, nuRho (rhoL L)
        (blockCov A Nb T (compMat fH (Sg σ ω)) σ - blockCov A Nb T (compMat fH (Cb σ)) σ)) ∂P := key
    _ ≤ (1 / 2) * 1 * ∫ ω, (∫ σ in Set.Icc (0 : ℝ) T,
          Kf (blk Nb T σ) ^ 2 * traceNormForm (Sg σ ω - Cb σ)) ∂P := by gcongr
    _ = _ := by ring

end HRS.Uniform.Comp28
