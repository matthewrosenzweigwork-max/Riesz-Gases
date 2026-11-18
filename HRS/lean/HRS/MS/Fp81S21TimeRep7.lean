import HRS.MS.Fp81S21TimeRep6
import HRS.MS.R26T8AS02a

/-! Measurable random L² classes represented by sample sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance (μ : Measure ℝ) : MeasurableSpace (Lp r26t6_Coeff 2 μ) := borel _
local instance (μ : Measure ℝ) : BorelSpace (Lp r26t6_Coeff 2 μ) := ⟨rfl⟩

/-- A jointly measurable field with square-integrable sample sections admits a
strongly measurable random L² class representing those sections. -/
theorem fp81s21_measurable_lp_sections
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ × Ω → r26t6_Coeff)
    (hgm : Measurable g)
    (hsec : ∀ᵐ ω ∂P, MemLp (fun t => g (t, ω)) 2 μ) :
    ∃ U : Ω → Lp r26t6_Coeff 2 μ,
      Measurable U ∧ StronglyMeasurable U ∧
      ∀ᵐ ω ∂P, ⇑(U ω) =ᵐ[μ] (fun t => g (t, ω)) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let V : Ω → Lp r26t6_Coeff 2 μ := fun ω =>
    if h : MemLp (fun t => g (t, ω)) 2 μ then h.toLp _ else 0
  have hV : ∀ᵐ ω ∂P, ⇑(V ω) =ᵐ[μ] (fun t => g (t, ω)) := by
    filter_upwards [hsec] with ω hω
    simpa [V, hω] using hω.coeFn_toLp
  have hVsm : AEStronglyMeasurable V P :=
    HRS.MS.R26T8A.r26t8a_s02a_sections P μ (fun ω t => g (t, ω))
      (hgm.comp measurable_swap).aestronglyMeasurable V hV
  refine ⟨hVsm.mk V, hVsm.measurable_mk, hVsm.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hVsm.ae_eq_mk, hV] with ω he hv
  rw [← he]
  exact hv

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_measurable_lp_sections
