import HRS.MS.R2InterpAux19
import HRS.MC.S7PIS2Cb

/-!
# S10.2 (worker S102), part 20 (packet G1): derivatives of the heat function of a projected functional

`D^j (r2HeatFn γ (Φ∘P) u) y [v] = s102_projHeatD γ Φ P j u y (P v)` (whole-space port of `s7_PIG_proj_deriv_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

/-- The projected derivative of the heat function without the projection on the arguments:
`(u,y) ↦ ∫ D^jΦ(P(y+z)) dγ_u(z)`. -/
def s102_projHeatD (γ : ℝ → Measure (OscPath d m T)) (Φ : OscPath d m T → ℝ)
    (P : OscPath d m T →L[ℝ] OscPath d m T) (j : ℕ) (u : ℝ) (y : OscPath d m T) :
    OscPath d m T [×j]→L[ℝ] ℝ :=
  ∫ z, iteratedFDeriv ℝ j Φ (P (y + z)) ∂(γ u)

theorem s102_integrable_of_bdd {F : Type*} [NormedAddCommGroup F] {μ : Measure (OscPath d m T)}
    [IsProbabilityMeasure μ] {f : OscPath d m T → F} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  Integrable.of_bound (C := C) hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem s102_bound_of_memCb {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Ψ : B → ℝ}
    (hΨ : MemCb 5 Ψ) {j : ℕ} (hj : j ≤ 5) : ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j Ψ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hΨ.2 j hj
  exact ⟨C, fun x => hC ⟨x, rfl⟩⟩

theorem s102_proj_deriv (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : OscPath d m T →L[ℝ] OscPath d m T) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 5)
    (u : ℝ) (y : OscPath d m T) (v : Fin j → OscPath d m T) :
    iteratedFDeriv ℝ j (r2HeatFn γ (fun w => Φ (P w)) u) y v = s102_projHeatD γ Φ P j u y (fun i => P (v i)) := by
  haveI := hγp u
  have hPΦ : MemCb 5 (fun w => Φ (P w)) := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof P hΦ).1
  have hA := ((s102_r2HeatFn_derivs γ u hPΦ).2 j hj y).1
  rw [hA]
  obtain ⟨C1, hC1⟩ := s102_bound_of_memCb hPΦ hj
  obtain ⟨C2, hC2⟩ := s102_bound_of_memCb hΦ hj
  have hcont1 : Continuous fun z : OscPath d m T => iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z) :=
    (hPΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).comp (by fun_prop)
  have hcont2 : Continuous fun z : OscPath d m T => iteratedFDeriv ℝ j Φ (P (y + z)) :=
    (hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)).comp (P.continuous.comp (by fun_prop))
  have hi1 : Integrable (fun z => iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) (γ u) :=
    s102_integrable_of_bdd hcont1 (fun z => hC1 _)
  have hi2 : Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) :=
    s102_integrable_of_bdd hcont2 (fun z => hC2 _)
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin j => OscPath d m T) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => OscPath d m T) ℝ v
  let L' : ContinuousMultilinearMap ℝ (fun _ : Fin j => OscPath d m T) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => OscPath d m T) ℝ (fun i => P (v i))
  have e1 : (∫ z, iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z) ∂(γ u)) v =
      ∫ z, L (iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) ∂(γ u) := by
    rw [L.integral_comp_comm hi1]; rfl
  have e2 : s102_projHeatD γ Φ P j u y (fun i => P (v i)) =
      ∫ z, L' (iteratedFDeriv ℝ j Φ (P (y + z))) ∂(γ u) := by
    rw [L'.integral_comp_comm hi2]; rfl
  rw [e1, e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (iteratedFDeriv ℝ j (fun w => Φ (P w)) (y + z)) v = (iteratedFDeriv ℝ j Φ (P (y + z))) (fun i => P (v i))
  have := ContinuousLinearMap.iteratedFDeriv_comp_right P hΦ.1 (y + z) (i := j) (by exact_mod_cast hj)
  change iteratedFDeriv ℝ j (Φ ∘ P) (y + z) v = _
  rw [this]
  rfl

end HRS.MS.R2Interp

end
