import HRS.Main.ThermCond

/-!
# MEANPART (flow): L0, thermal density of `ρ ≡ 1`

`mp_withDensityReal_one`, `mp_thermalDensity_one` (packet `mpflow`, plan `docs/MAIN_A_PLAN_mean_particles.md`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem mp_withDensity_one : withDensityReal (fun _ : Torus d => (1 : ℝ)) = volume := by
  unfold withDensityReal
  simp

theorem mp_thermalDensity_one (g : Torus d → ℝ) (β : ℝ) :
    IsThermalDensity g (fun _ => 0) β (fun _ => (1 : ℝ)) := by
  have hc : ∀ x : Torus d, convFun g (fun _ => (1 : ℝ)) x = ∫ y, g y := by
    intro x
    unfold convFun
    simp only [mul_one]
    exact integral_sub_left_eq_self g volume x
  refine ⟨⟨fun _ => zero_le_one, measurable_const, by simp⟩, fun x => ?_⟩
  simp only [hc, zero_add, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hpos : 0 < Real.exp (-β * ∫ y, g y) := Real.exp_pos _
  exact (div_self hpos.ne').symm

end Main

end HRS
