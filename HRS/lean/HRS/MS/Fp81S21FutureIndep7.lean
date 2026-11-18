import HRS.MS.Fp81S21FutureIndep5
import HRS.MS.R2InterpAux5
import HRS.MS.GenPathAux42

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.GenPath HRS.MS.R2Interp

/-- The continuous-path future law is uniquely determined by its R2 covariance
at the same absolute cutoff. -/
theorem fp81s21_future_path_law_unique {d : ℕ} {m H r : ℝ}
    (hH : 0 ≤ H) (C : WholeCoeff d)
    (γ γ' : Measure (OscPath d m H)) [IsProbabilityMeasure γ]
    [IsProbabilityMeasure γ'] (hγ : IsR2FutureGaussian C m H r γ)
    (hγ' : IsR2FutureGaussian C m H r γ') : γ = γ' := by
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH⟩⟩
  let s : ℕ → Icc (0 : ℝ) H := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  let Ψ := s56PathCoords (d := d) m H s
  have hΨm : Measurable Ψ := s56_measurable_pathCoords m H s
  apply (s56_measurableEmbedding_pathCoords m H s hs).map_injective
  apply s56_seq_law_eq γ γ' Ψ Ψ hΨm.aemeasurable hΨm.aemeasurable
  intro n f hf
  let τ : Fin n → Icc (0 : ℝ) H := fun i => s (f i).1
  let α : Fin n → MultiIndex d := fun i => (f i).2
  have hl := (s102_obs_law C hγ τ α).2
  have hl' := (s102_obs_law C hγ' τ α).2
  have heq := hl.trans hl'.symm
  have hobs : (s102_obs τ α : OscPath d m H → EuclideanSpace ℝ (Fin n)) =
      (fun w => WithLp.toLp 2 (fun i => OscDual.coord (OscPath.at' w (τ i)) (α i))) := by
    funext w
    ext i
    exact s102_obs_apply τ α w i
  rw [hobs] at heq
  simpa only [Ψ, s56PathCoords, τ, α] using heq

#print axioms fp81s21_future_path_law_unique

end HRS.Fp81.S21
end
