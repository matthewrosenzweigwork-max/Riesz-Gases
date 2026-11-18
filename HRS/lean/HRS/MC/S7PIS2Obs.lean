import HRS.MC.S7PIDefs
import HRS.Main.A33Aux14

/-!
# Packet piS2, part 3: `s7_PIS_obs_clm` (the observation map is a continuous linear map)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIS2_eval_smul {m : ℝ} (c : ℝ) (F : NegSobolev d m) (ψ : Torus d → ℝ) :
    NegSobolev.eval (c • F) ψ = c * NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hc : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := by
    unfold NegSobolev.coord; rfl
  unfold NegSobolev.fourierCoeff
  rw [hc]
  ring

theorem S7PIS2_pathAt_add {m T : ℝ} (w w' : PathSpace d m T) (s : ℝ) :
    pathAt (w + w') s = pathAt w s + pathAt w' s := by
  unfold pathAt
  split_ifs with h
  · rfl
  · simp

theorem S7PIS2_pathAt_smul {m T : ℝ} (c : ℝ) (w : PathSpace d m T) (s : ℝ) :
    pathAt (c • w) s = c • pathAt w s := by
  unfold pathAt
  split_ifs with h
  · rfl
  · simp

theorem S7PIS2_norm_pathAt_le {m T : ℝ} (w : PathSpace d m T) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖pathAt w s‖ ≤ ‖w‖ := by
  unfold pathAt
  rw [dif_pos hs]
  exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) ⟨s, hs⟩

/-- The `i`-th observation functional, as a continuous linear functional on the path space. -/
def S7PIS2_obsFun (m T : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) : PathSpace d m T →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => NegSobolev.eval (pathAt w s) ψ
      map_add' := fun w w' => by
        rw [S7PIS2_pathAt_add]
        exact HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth m hψ)
      map_smul' := fun c w => by
        rw [S7PIS2_pathAt_smul, S7PIS2_eval_smul]
        rfl }
    (sobolevNorm m ψ) (fun w => by
      refine (HRS.A33.a33_abs_eval_le _ (HRS.A33.a33_ws_smooth m hψ)).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (S7PIS2_norm_pathAt_le w hs) (Real.sqrt_nonneg _))

theorem s7_PIS_obs_clm_proof (m T : ℝ) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∃ O : PathSpace d m T →L[ℝ] EuclideanSpace ℝ (Fin q), ∀ w, O w = obsVec m T t φ w :=
  ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i => S7PIS2_obsFun m T (ht i) (hφ i)), fun w => rfl⟩

end HRS.MC.Sec7.S7PIS2

end
