import HRS.Uniform.Q45VM

/-!
# Q45 (Lemma 3.20): transport of the path tensors along an isometric embedding `E' ↪ E`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Push

variable {E' E : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Post-composition of paths with a continuous linear map. -/
def pathPush (T : ℝ) (ι : E' →L[ℝ] E) : PathSp T E' →L[ℝ] PathSp T E :=
  ι.compLeftContinuous ℝ (Set.Icc (0 : ℝ) T)

lemma pcm_pathPush {T : ℝ} (ι : E' →L[ℝ] E) (y : PathSp T E') (t : Set.Icc (0 : ℝ) T) :
    pcm (pathPush T ι y) t = ι (pcm y t) := rfl

lemma norm_pathPush_le {T : ℝ} (ι : E' →ₗᵢ[ℝ] E) : ‖pathPush T ι.toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine norm_pcm_le _ (norm_nonneg y) fun t => ?_
  have : ‖pcm (pathPush T ι.toContinuousLinearMap y) t‖ = ‖pcm y t‖ := by
    rw [pcm_pathPush]; exact ι.norm_map _
  exact this.le.trans (norm_pcm_apply_le y t)

end Push

end HRS.Uniform.Q45
