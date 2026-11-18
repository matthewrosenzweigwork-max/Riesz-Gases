import HRS.MC.S7PIDefs
import HRS.MC.S7PIA
import HRS.MC.S7PIS2Cb

/-!
# Packet piG, part G1: derivatives of the heat function of a projected functional

`s7_PIG_proj_deriv_proof`: `D^j (heatFn γ (Φ∘P) u) y [v] = projHeatD γ Φ P j u y (P v)`.  Namespace `HRS.MC.Sec7.S7PIG1`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- second countability of the path space (local instance) -/
local instance S7PIG1_sc {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- a continuous bounded function into a normed group is integrable for a probability measure -/
theorem S7PIG1_integrable_of_bdd {m T : ℝ} {F : Type*} [NormedAddCommGroup F] {μ : Measure (PathSpace d m T)}
    [IsProbabilityMeasure μ] {f : PathSpace d m T → F} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound (C := C) hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem S7PIG1_bound_of_memCb {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Ψ : B → ℝ}
    (hΨ : MemCb 5 Ψ) {j : ℕ} (hj : j ≤ 5) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j Ψ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΨ.2 j hj
  exact ⟨C, fun x => hC ⟨x, rfl⟩⟩

theorem s7_PIG_proj_deriv_proof {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : PathSpace d m T →L[ℝ] PathSpace d m T) {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 5)
    (u : ℝ) (y : PathSpace d m T) (v : Fin j → PathSpace d m T) :
    iteratedFDeriv ℝ j (heatFn γ (fun w => Φ (P w)) u) y v = projHeatD γ Φ P j u y (fun i => P (v i)) := by
  have := hγp u
  have hPΦ : MemCb 5 (fun w => Φ (P w)) := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof P hΦ).1
  have hA := ((HRS.MC.Sec7.PIA.s7_PI_A_heat_derivs_proof (γ u) hPΦ u).2 j hj y).1
  have hfun : heatFn γ (fun w => Φ (P w)) u = heatFn (fun _ => γ u) (fun w => Φ (P w)) u := rfl
  rw [hfun, hA]
  obtain ⟨C1, hC1⟩ := S7PIG1_bound_of_memCb hPΦ hj
  obtain ⟨C2, hC2⟩ := S7PIG1_bound_of_memCb hΦ hj
  have hcont1 : Continuous fun z : PathSpace d m T => iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z) :=
    (hPΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).comp (by fun_prop)
  have hcont2 : Continuous fun z : PathSpace d m T => iteratedFDeriv ℝ j Φ (P (y + z)) :=
    (hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).comp (P.continuous.comp (by fun_prop))
  have hi1 : Integrable (fun z => iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) (γ u) :=
    S7PIG1_integrable_of_bdd hcont1 (fun z => hC1 _)
  have hi2 : Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) :=
    S7PIG1_integrable_of_bdd hcont2 (fun z => hC2 _)
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin j => PathSpace d m T) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PathSpace d m T) ℝ v
  let L' : ContinuousMultilinearMap ℝ (fun _ : Fin j => PathSpace d m T) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => PathSpace d m T) ℝ (fun i => P (v i))
  have e1 : (∫ z, iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z) ∂(γ u)) v =
      ∫ z, L (iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) ∂(γ u) := by
    rw [L.integral_comp_comm hi1]; rfl
  have e2 : projHeatD γ Φ P j u y (fun i => P (v i)) =
      ∫ z, L' (iteratedFDeriv ℝ j Φ (P (y + z))) ∂(γ u) := by
    rw [L'.integral_comp_comm hi2]; rfl
  rw [e1, e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) v = (iteratedFDeriv ℝ j Φ (P (y + z))) (fun i => P (v i))
  have := ContinuousLinearMap.iteratedFDeriv_comp_right P hΦ.1 (y + z) (i := j) (by exact_mod_cast hj)
  change iteratedFDeriv ℝ j (Φ ∘ P) (y + z) v = _
  rw [this]
  rfl

end HRS.MC.Sec7.S7PIG1

end
