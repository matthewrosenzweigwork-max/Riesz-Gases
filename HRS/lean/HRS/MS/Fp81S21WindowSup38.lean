import HRS.MS.Fp81S21WindowSup37

/-! Measurable sections of a jointly measurable field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21

/-- Every parameter section of a jointly measurable field is measurable. -/
theorem fp81s21_measurable_parameter_section
    {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace E]
    (F : S × Ω → E) (hF : Measurable F) (s : S) :
    Measurable (fun ω => F (s, ω)) := by
  exact hF.comp (measurable_const.prodMk measurable_id)

#print axioms fp81s21_measurable_parameter_section
end HRS.Fp81.S21
end
