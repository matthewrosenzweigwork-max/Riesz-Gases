import HRS.Uniform.Q45Blocks3

/-!
# Q45: Lindeberg comparison of block transforms
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {m q : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma s1Norm_zero {p : ℕ} : s1Norm (0 : Matrix (Fin p) (Fin p) ℝ) = 0 := by
  unfold s1Norm traceNormMatrix
  simp

lemma pairNorm_zero {p : ℕ} {ν : Matrix (Fin p) (Fin p) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν) :
    ν 0 = 0 := by
  have h1 := hν.le_s1 0
  have h2 := hν.nonneg 0
  rw [s1Norm_zero, mul_zero] at h1
  exact le_antisymm h1 h2

section Comparison

variable {ℱ : Filtration ℝ mΩ} {T : ℝ} {Nb : ℕ} {A : ℕ → Matrix (Fin m) (Fin q) ℝ}

/-- The Gaussian block covariance `σ ↦ A_{k(σ)} C_σ A_{k(σ)}ᵀ` is measurable, trace-norm integrable and positive
semidefinite on `[0,T]`. -/
lemma blockCov_det_props (hT : 0 < T) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ k (u : Fin q → ℝ), ((A k).mulVec u) ⬝ᵥ ((A k).mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u))
    {Cq : ℝ → Matrix (Fin q) (Fin q) ℝ} {N' : ℝ → Ω → ℝ^q}
    (hN' : IsVectorMartingaleWithCovariation P ℱ T N' (fun σ _ => Cq σ)) :
    Measurable (fun σ => blockCov A Nb T (Cq σ) σ) ∧
    IntegrableOn (fun σ => s1Norm (blockCov A Nb T (Cq σ) σ)) (Set.Icc 0 T) ∧
    ∀ σ ∈ Set.Icc (0 : ℝ) T, (blockCov A Nb T (Cq σ) σ).PosSemidef := by
  obtain ⟨ω₀⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  have hmeasC : ∀ c c' : Fin q, Measurable fun σ : ℝ => Cq σ c c' := fun c c' =>
    (measurable_pi_apply c').comp ((measurable_pi_apply c).comp
      (hN'.sigma_meas.comp (measurable_id.prodMk (measurable_const (a := ω₀)))))
  have hm : Measurable (fun σ => blockCov A Nb T (Cq σ) σ) :=
    measurable_blockCov A Nb T id measurable_id _ hmeasC
  refine ⟨hm, ?_, ?_⟩
  · obtain ⟨ω, hω⟩ := (hN'.sigma_pathint).exists
    exact Integrable.mono' (hω.const_mul (c ^ 2))
      (continuous_s1Norm.measurable.comp hm).aestronglyMeasurable
      (ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _)]
        exact s1Norm_conj_le (A (blk Nb T σ)) hc (hA _) _)
  · obtain ⟨ω, hω⟩ := (hN'.sigma_psd).exists
    intro σ hσ
    have := (hω σ hσ).mul_mul_conjTranspose_same (A (blk Nb T σ))
    simpa [blockCov, Matrix.conjTranspose_eq_transpose_of_trivial] using this

/-- **Lindeberg comparison for block-constant integrands.**  For `ℝ^q`-valued vector martingales `N` (random
covariation `Sq`) and `N'` (deterministic covariation `Cq`), block matrices `A_k : ℝ^q → ℝ^m`, an `ℱ₀`-measurable shift `ξ`,
and a test function `h` with Hessian-pairing bound `Hp ν`, the laws of `ξ + 𝒮^N_T` and `ξ + 𝒮^{N'}_T` differ by at most
`½ Hp E ∫ ν(A(Sq - Cq)Aᵀ)`. -/
theorem blocks_comparison (hT : 0 < T) (hNb : 1 ≤ Nb) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ k (u : Fin q → ℝ), ((A k).mulVec u) ⬝ᵥ ((A k).mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u))
    {N N' : ℝ → Ω → ℝ^q} {Sq : ℝ → Ω → Matrix (Fin q) (Fin q) ℝ}
    {Cq : ℝ → Matrix (Fin q) (Fin q) ℝ}
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq)
    (hN' : IsVectorMartingaleWithCovariation P ℱ T N' (fun σ _ => Cq σ))
    (ξ : Ω → ℝ^m) (hξ : StronglyMeasurable[ℱ 0] ξ)
    (h : (ℝ^m) → ℝ) (hh : ContDiff ℝ 2 h) (H Hp B0 G1 : ℝ) (hHp : 0 ≤ Hp)
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (hB0 : ∀ x, |h x| ≤ B0) (hG1 : ∀ x, ‖fderiv ℝ h x‖ ≤ G1)
    {ν : Matrix (Fin m) (Fin m) ℝ → ℝ} {Cν : ℝ} (hν : PairNorm ν Cν)
    (hpair : ∀ x Q', |hessPair h x Q'| ≤ Hp * ν Q') :
    |∫ ω, h (ξ ω + blockProc A Nb T N T ω) ∂P - ∫ ω, h (ξ ω + blockProc A Nb T N' T ω) ∂P| ≤
      (1 / 2) * Hp * ∫ ω, (∫ σ in Set.Icc 0 T,
        ν (blockCov A Nb T (Sq σ ω) σ - blockCov A Nb T (Cq σ) σ)) ∂P := by
  obtain ⟨hsbm, hsbi, hsbp⟩ := blockCov_det_props P hT hc hA (Nb := Nb) hN'
  set nn : ℕ → ℕ := fun ℓ => Nb * (ℓ + 1) with hnn
  have hnnt : Tendsto nn atTop atTop := by
    refine tendsto_atTop_mono (fun ℓ => ?_) (tendsto_add_atTop_nat 1)
    simp only [hnn]
    nlinarith
  have hn1 : ∀ ℓ, 1 ≤ nn ℓ := fun ℓ => by simp only [hnn]; nlinarith
  have hadm : ∀ ℓ, ∀ k < nn ℓ, (fun τ τ' => ∃ k < Nb, rr Nb T k ≤ τ ∧ τ' ≤ rr Nb T (k + 1))
      (unifPart T (nn ℓ) k) (unifPart T (nn ℓ) (k + 1)) :=
    fun ℓ k hk => cell_in_block hT.le hNb ℓ k hk
  have hI := cellIface_block P hT hNb hc hA hN
  have hI' := cellIface_block P hT hNb hc hA hN'
  have r1 := clt_gen P ℱ T hT.le (blockProc A Nb T N) _ hI (fun σ => blockCov A Nb T (Cq σ) σ) hsbm
    hsbi hsbp hν ξ hξ h hh H Hp B0 G1 hHp hH hB0 hG1 hpair nn hnnt hn1 hadm
    (fun H' L' hH' hL' => blockProc_tendsto P hT hNb hc hA hN H' L' hH' hL')
  have r2 := clt_gen P ℱ T hT.le (blockProc A Nb T N') _ hI' (fun σ => blockCov A Nb T (Cq σ) σ) hsbm
    hsbi hsbp hν ξ hξ h hh H Hp B0 G1 hHp hH hB0 hG1 hpair nn hnnt hn1 hadm
    (fun H' L' hH' hL' => blockProc_tendsto P hT hNb hc hA hN' H' L' hH' hL')
  have hz : ∫ ω, (∫ σ in Set.Icc 0 T, ν (blockCov A Nb T (Cq σ) σ - blockCov A Nb T (Cq σ) σ)) ∂P = 0 := by
    simp [sub_self, pairNorm_zero hν]
  rw [hz, mul_zero] at r2
  have r2' := abs_nonpos_iff.1 r2
  rw [abs_le] at r1 ⊢
  constructor <;> linarith [r1.1, r1.2, sub_eq_zero.1 r2']

end Comparison

end HRS.Uniform.Q45
