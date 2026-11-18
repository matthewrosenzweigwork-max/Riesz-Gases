import HRS.MS.Fp81S21TimeRep9
import HRS.MS.Fp81S21TimeShift

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.MS.R26T6

local instance fp81s21_IntervalHistoryRep_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_IntervalHistoryRep_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩
local instance fp81s21_IntervalHistoryRep_inst3 (H : ℝ) : MeasurableSpace (r26t6_TimeCoeff H) := borel _
local instance fp81s21_IntervalHistoryRep_inst4 (H : ℝ) : BorelSpace (r26t6_TimeCoeff H) := ⟨rfl⟩

/-- Convert a coefficient-valued `L²` history to its `L¹` coefficient
representative, retaining the chart action almost everywhere in time. -/
theorem fp81s21_TimeL2Rep_toL1_chart
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (q : ℝ → Ω → r26t6_Coeff) (M b H : ℝ) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeL2Rep P q M b H U) :
    Measurable (fun ω => fp81s21_timeL2L1 H hH (U ω)) ∧
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) H)), ∀ f : Euc d → ℝ,
      r26t6_coefficientField E (fp81s21_timeL2L1 H hH (U ω)) s f =
        fp81s21_chartAction E (q (b + s) ω) f := by
  refine ⟨(fp81s21_timeL2L1 H hH).measurable.comp hU.1, ?_⟩
  filter_upwards [hU.2.2.2] with ω hω
  rcases hω with ⟨_, hsection⟩
  have hrep : fp81s21_timeL2L1 H hH (U ω) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)]
      fun s => q (b + s) ω :=
    (fp81s21_timeL2L1_ae H hH (U ω)).trans hsection
  filter_upwards [hrep] with s hs
  intro f
  change inner ℝ (fp81s21_timeL2L1 H hH (U ω) s) (E.encode f) =
    inner ℝ (q (b + s) ω) (E.encode f)
  exact congrArg (fun z : r26t6_Coeff => inner ℝ z (E.encode f)) hs

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_TimeL2Rep_toL1_chart
