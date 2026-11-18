import HRS.MS.R2SeAux46

/-!
# S9.9 `r2_static_edgeworth`, packet 47: the Gaussian on `B_m` (inverse of `s45_gauss_transport`)

Worker S99, namespace `S99`.  `s99_gauss_back`: if `G'` is a centered Gaussian on `ℓ²` with covariance
`λ_i^{-m/2} λ_j^{-m/2} C(h_{e i}, h_{e j})` then `G'.map Ψ⁻¹` is `IsCenteredGaussianOsc m _ C`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_gauss_back (m : ℕ) (e : ℕ ≃ MultiIndex d) {G' : Measure SeqL2}
    {Cv : (Euc d → ℝ) → (Euc d → ℝ) → ℝ}
    (hG : IsCenteredGaussianSeq G' fun i j => oscEigenvalue d (e i) ^ (-((m : ℝ) / 2)) *
      oscEigenvalue d (e j) ^ (-((m : ℝ) / 2)) * Cv (hermiteFunD (e i)) (hermiteFunD (e j))) :
    IsCenteredGaussianOsc (m : ℝ) (G'.map (s45_Psi (m : ℝ) e).symm) Cv := by
  obtain ⟨⟨hGG, hcen⟩, hcov⟩ := hG
  have hΨm : Measurable (s45_Psi (m : ℝ) e).symm := (s45_Psi (m : ℝ) e).symm.continuous.measurable
  refine ⟨⟨?_, fun L => ?_⟩, fun α β => ?_⟩
  · exact isGaussian_map_equiv (μ := G') (s45_Psi (m : ℝ) e).symm.toContinuousLinearEquiv
  · rw [integral_map hΨm.aemeasurable L.continuous.aestronglyMeasurable]
    have := hcen (L.comp (s45_Psi (m : ℝ) e).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    simpa using this
  · have hcoord : ∀ (z : SeqL2) (α : MultiIndex d), OscDual.coord ((s45_Psi (m : ℝ) e).symm z) α =
        SeqL2.coord z (e.symm α) := fun z α => by
      have := s45_Psi_coord (m : ℝ) e ((s45_Psi (m : ℝ) e).symm z) (e.symm α)
      rw [LinearIsometryEquiv.apply_symm_apply] at this
      rw [this]; simp
    have hform : ∀ z : SeqL2, OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) α *
        OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) β =
        (oscEigenvalue d α ^ ((m : ℝ) / 2) * oscEigenvalue d β ^ ((m : ℝ) / 2)) *
          (SeqL2.coord z (e.symm α) * SeqL2.coord z (e.symm β)) := fun z => by
      unfold OscDual.hermiteCoeff
      rw [hcoord, hcoord]; ring
    have hcm : AEStronglyMeasurable (fun F : OscDual d (m : ℝ) =>
        OscDual.hermiteCoeff F α * OscDual.hermiteCoeff F β) (G'.map (s45_Psi (m : ℝ) e).symm) := by
      have hc : Continuous fun F : OscDual d (m : ℝ) => OscDual.coord F α := by
        have : (fun F : OscDual d (m : ℝ) => OscDual.coord F α) =
            fun F => inner ℝ (lp.single (E := fun _ : MultiIndex d => ℝ) 2 α (1 : ℝ)) (show lp (fun _ : MultiIndex d => ℝ) 2 from F) := by
          funext F
          rw [lp.inner_single_left]; simp [OscDual.coord]
        rw [this]; exact continuous_const.inner continuous_id
      have hcb : Continuous fun F : OscDual d (m : ℝ) => OscDual.coord F β := by
        have : (fun F : OscDual d (m : ℝ) => OscDual.coord F β) =
            fun F => inner ℝ (lp.single (E := fun _ : MultiIndex d => ℝ) 2 β (1 : ℝ)) (show lp (fun _ : MultiIndex d => ℝ) 2 from F) := by
          funext F
          rw [lp.inner_single_left]; simp [OscDual.coord]
        rw [this]; exact continuous_const.inner continuous_id
      unfold OscDual.hermiteCoeff
      exact ((continuous_const.mul hc).mul (continuous_const.mul hcb)).aestronglyMeasurable
    obtain ⟨hint, hval⟩ := hcov (e.symm α) (e.symm β)
    refine ⟨(integrable_map_measure hcm hΨm.aemeasurable).2 ?_, ?_⟩
    · have : (fun z : SeqL2 => OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) α *
          OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) β) = fun z =>
          (oscEigenvalue d α ^ ((m : ℝ) / 2) * oscEigenvalue d β ^ ((m : ℝ) / 2)) *
            (SeqL2.coord z (e.symm α) * SeqL2.coord z (e.symm β)) := funext hform
      show Integrable (fun z : SeqL2 => OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) α *
          OscDual.hermiteCoeff ((s45_Psi (m : ℝ) e).symm z) β) G'
      rw [this]
      exact hint.const_mul _
    · rw [integral_map hΨm.aemeasurable hcm]
      simp_rw [hform]
      rw [integral_const_mul, hval]
      simp only [Equiv.apply_symm_apply]
      have h1 := rpow_neg_half_mul (m : ℝ) _ (oscEv_pos α)
      have h2 := rpow_neg_half_mul (m : ℝ) _ (oscEv_pos β)
      calc oscEigenvalue d α ^ ((m : ℝ) / 2) * oscEigenvalue d β ^ ((m : ℝ) / 2) *
          (oscEigenvalue d α ^ (-((m : ℝ) / 2)) * oscEigenvalue d β ^ (-((m : ℝ) / 2)) *
            Cv (hermiteFunD α) (hermiteFunD β))
          = ((oscEigenvalue d α ^ (-((m : ℝ) / 2)) * oscEigenvalue d α ^ ((m : ℝ) / 2)) *
            (oscEigenvalue d β ^ (-((m : ℝ) / 2)) * oscEigenvalue d β ^ ((m : ℝ) / 2))) *
            Cv (hermiteFunD α) (hermiteFunD β) := by ring
        _ = _ := by rw [h1, h2]; ring

end S99

end
