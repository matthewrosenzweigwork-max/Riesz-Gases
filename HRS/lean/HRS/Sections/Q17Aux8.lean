import HRS.Sections.Q17Aux7

noncomputable section

open MeasureTheory Filter Topology


namespace HRS.Sec7

variable {d : ℕ}

theorem projection_strong_proof (m T : ℝ) (hT : 0 < T) :
    ∃ Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T),
      (∀ L w, Pj L w = projPoly m T hT.le L w) ∧ (∀ L, ‖Pj L‖ ≤ 1) ∧
      (∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) ∧
      ∀ (j : ℕ) (v : TensorDual (PathSpace d m T) j), v ∈ projTensor (PathSpace d m T) j →
        Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v) := by
  refine ⟨fun L => LinearMap.mkContinuous (q17_projLin m T hT L) 1
    (fun w => by rw [one_mul]; exact q17_projPoly_norm_le hT L w), ?_, ?_, ?_, ?_⟩
  · intro L w
    rfl
  · intro L
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · intro w
    exact q17_projPoly_tendsto hT w
  · intro j v hv
    refine q17_tensorPow_tendsto (fun L => LinearMap.mkContinuous (q17_projLin m T hT L) 1
      (fun w => by rw [one_mul]; exact q17_projPoly_norm_le hT L w)) ?_ ?_ j v hv
    · intro L
      exact LinearMap.mkContinuous_norm_le _ zero_le_one _
    · intro w
      exact q17_projPoly_tendsto hT w

end HRS.Sec7

example := (@HRS.Sec7.projection_strong_proof : type_of% @HRS.Sec7.projection_strong)
