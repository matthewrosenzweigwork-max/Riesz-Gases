import HRS.MS.Fp81S21WindowSup27

/-! Restriction of a measurable parameterized field to a subtype. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21

/-- Restrict the first argument of a jointly measurable function to any subtype. -/
theorem fp81s21_measurable_restrict_parameter
    {S E F : Type*} [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]
    {A : Set S} {f : S × E → F} (hf : Measurable f) :
    Measurable (fun q : A × E => f (q.1.1, q.2)) := by
  exact hf.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

#print axioms fp81s21_measurable_restrict_parameter
end HRS.Fp81.S21
end
