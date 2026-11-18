import HRS.MS.Fp81S21WindowSup46

/-! Measurable zero extension of a parameterized field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- A jointly measurable field on a measurable parameter set admits a jointly
measurable extension by zero to the full parameter space. -/
theorem fp81s21_param_measurable_zero_extension
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {B : Set S} (hB : MeasurableSet B)
    (g : B × Ω → ℝ) (hg : Measurable g) :
    ∃ G : S × Ω → ℝ, Measurable G ∧
      (∀ b : B, ∀ ω, G (b.1, ω) = g (b, ω)) ∧
      ∀ z : S × Ω, z.1 ∉ B → G z = 0 := by
  let A : Set (S × Ω) := {z | z.1 ∈ B}
  have hA : MeasurableSet A := hB.preimage measurable_fst
  let j : A → B × Ω := fun z => (⟨z.1.1, z.2⟩, z.1.2)
  have hj : Measurable j := by
    exact ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_snd.comp measurable_subtype_coe)
  have hemb : MeasurableEmbedding ((↑) : A → S × Ω) := MeasurableEmbedding.subtype_coe hA
  obtain ⟨F, hF, hFe⟩ := hemb.exists_measurable_extend (hg.comp hj) (fun _ => ⟨(0 : ℝ)⟩)
  let G := A.indicator F
  refine ⟨G, hF.indicator hA, ?_, ?_⟩
  · intro b ω
    have hz : (b.1, ω) ∈ A := b.2
    have h := congrFun hFe ⟨(b.1, ω), hz⟩
    simpa [G, Set.indicator_of_mem hz, j, Function.comp_def] using h
  · intro z hz
    have hz' : z ∉ A := hz
    exact Set.indicator_of_notMem hz' F

#print axioms fp81s21_param_measurable_zero_extension
end HRS.Fp81.S21
end
