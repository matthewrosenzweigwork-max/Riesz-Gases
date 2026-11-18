import HRS.MS.WsInitHAux3

/-!
# S21H packet H, part 4: coordinate schemes from finite-dimensional subspaces of a Hilbert space

`s21h_scheme_of_subspace`: for a finite-dimensional subspace `K` of a real inner product space `E` there are `c : E →L ℝ^{dim K}`,
`e : ℝ^{dim K} →L E`, both of norm `≤ 1`, with `e (c v) = P_K v` (orthogonal projection).  Together with `s21h_w1_abstract` this reduces
the projection hypothesis `hscheme` to the tail bounds of `∫ ‖v - P_{K_Q} v‖` (`s21h_w1_of_subspaces`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

section Subspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem s21h_scheme_of_subspace (K : Submodule ℝ E) [FiniteDimensional ℝ K] :
    ∃ (c : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ K)))
      (e : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) →L[ℝ] E),
      ‖c‖ ≤ 1 ∧ ‖e‖ ≤ 1 ∧ ∀ v, e (c v) = K.starProjection v := by
  haveI : CompleteSpace K := FiniteDimensional.complete ℝ K
  set b := stdOrthonormalBasis ℝ K with hb
  set R : K →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
    b.repr.toLinearIsometry.toContinuousLinearMap with hR
  set R' : EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) →L[ℝ] K :=
    b.repr.symm.toLinearIsometry.toContinuousLinearMap with hR'
  refine ⟨R.comp K.orthogonalProjectionOnto, K.subtypeL.comp R', ?_, ?_, fun v => ?_⟩
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖R‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
    have h2 := K.orthogonalProjectionOnto_norm_le
    calc ‖R‖ * ‖K.orthogonalProjectionOnto‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖R'‖ ≤ 1 := LinearIsometry.norm_toContinuousLinearMap_le _
    have h2 : ‖K.subtypeL‖ ≤ 1 := Submodule.norm_subtypeL_le K
    calc ‖K.subtypeL‖ * ‖R'‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  · simp [R, R']

end Subspace

section Glue

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X]

/-- The abstract `W_1` rate with the projection hypothesis given by finite-dimensional subspaces `K_Q` of the Hilbert space `E`:
`dim K_Q ≤ K Q²` and `∫ ‖v - P_{K_Q} v‖ ≤ τ Q^{-3/4}` for both laws. -/
theorem s21h_w1_of_subspaces (ι : E →L[ℝ] X) (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) {δ A₁ A₂ K τ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hcomp : S21hDerivComp μ γ (Real.sqrt δ) A₁ A₂)
    (hsub : ∀ Q : ℕ, 1 ≤ Q → ∃ (K' : Submodule ℝ E) (_ : FiniteDimensional ℝ K'),
        (Module.finrank ℝ K' : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∫⁻ v, ‖v - K'.starProjection v‖ₑ ∂μ ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4)) ∧
        ∫⁻ v, ‖v - K'.starProjection v‖ₑ ∂γ ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4))) :
    wassersteinE 1 (μ.map ι) (γ.map ι) ≤
      ENNReal.ofReal (‖ι‖ * ((2 * τ + 4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20))) := by
  refine s21h_w1_abstract ι μ γ hμ2 hγ2 hδ0 hδ1 hA₁ hA₂ hK hτ hcomp fun Q hQ => ?_
  obtain ⟨K', hfd, hr, ht1, ht2⟩ := hsub Q hQ
  obtain ⟨c, e, hc, he, hce⟩ := s21h_scheme_of_subspace K'
  refine ⟨_, c, e, hc, he, hr, ?_, ?_⟩
  · simpa only [hce] using ht1
  · simpa only [hce] using ht2

end Glue

end HRS.MS.S21
