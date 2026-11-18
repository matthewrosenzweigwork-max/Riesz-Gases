import HRS.MS.R26T6CI09

/-!
# I11: exact coordinatewise Bochner integral identity in OscDual

This is needed to recover every historical stochastic oscillator
coordinate from an L³ primitive and the scalar fundamental theorem
of calculus.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ} {m : ℝ}

local instance instR26T6CI11OscFactTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem r26t6c_oscCoord_integral
    (t : ℝ) (G : ℝ → OscDual d m)
    (hG : IntegrableOn G (Set.Icc (0 : ℝ) t))
    (α : MultiIndex d) :
    OscDual.coord (∫ v in Set.Icc (0 : ℝ) t, G v) α =
      ∫ v in Set.Icc (0 : ℝ) t, OscDual.coord (G v) α := by
  let ev : OscDual d m →L[ℝ] ℝ :=
    lp.evalCLM ℝ (fun _ : MultiIndex d => ℝ) 2 α
  have h := (ev.integral_comp_comm hG).symm
  change OscDual.coord (∫ v in Set.Icc (0 : ℝ) t, G v) α =
    ∫ v in Set.Icc (0 : ℝ) t, OscDual.coord (G v) α at h
  exact h

end HRS.MS.R26T6C
