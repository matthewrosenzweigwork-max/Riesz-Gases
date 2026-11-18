import HRS.MS.Fp81S21WindowSup32

/-! Measurable substitution for a raw parameterized field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21

/-- Substitution of a jointly measurable random parameter into a measurable field. -/
theorem fp81s21_param_comp_meas
    {S Ω E F : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (f : S × E → F) (Y : S × Ω → E)
    (hf : Measurable f) (hY : Measurable Y) :
    Measurable (fun z : S × Ω => f (z.1, Y z)) := by
  exact hf.comp (measurable_fst.prodMk hY)

#print axioms fp81s21_param_comp_meas
end HRS.Fp81.S21
end
