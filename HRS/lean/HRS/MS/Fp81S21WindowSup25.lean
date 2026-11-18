import HRS.MS.Fp81S21WindowSup24

/-! Measurable substitution and centering for parameterized random fields. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21

/-- Substitution into a jointly measurable field followed by actual-law centering. -/
theorem fp81s21_param_centered_comp_meas
    {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] (F : S × E → ℝ) (Y : S × Ω → E)
    (hF : Measurable F) (hY : Measurable Y) (c : ℝ) :
    Measurable (fun z : S × Ω => c *
      (F (z.1, Y z) - ∫ ω, F (z.1, Y (z.1, ω)) ∂P)) := by
  let G : S × Ω → ℝ := fun z => F (z.1, Y z)
  have hG : Measurable G := hF.comp (measurable_fst.prodMk hY)
  have hmean : Measurable (fun s : S => ∫ ω, G (s, ω) ∂P) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  exact measurable_const.mul (hG.sub (hmean.comp measurable_fst))

#print axioms fp81s21_param_centered_comp_meas
end HRS.Fp81.S21
end
