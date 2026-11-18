import HRS.MS.Fp81S21TimeRep8

/-! Coefficient-section contract for moment representatives. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.MS.R26T6

local instance (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The coefficient-only measurable time-section contract. -/
def fp81s21_TimeL2Rep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) : Prop :=
  Measurable U ∧ MemLp U 2 P ∧
    (∫ ω, ‖U ω‖ ^ 2 ∂P) ≤ H * M ∧
    ∀ᵐ ω ∂P,
      MemLp (fun t => q (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) H)) ∧
      ⇑(U ω) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) H)] (fun t => q (a + t) ω)

/-- A moment representative determines a measurable time-L² section class. -/
theorem fp81s21_MomentRep_time_section
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ) (q : ℝ → Ω → r26t6_Coeff)
    (M a H : ℝ) (hrep : fp81s21_MomentRep E P Q q M)
    (ha : 0 ≤ a) (hH : 0 ≤ H) :
    ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep P q M a H U := by
  let g : ℝ × Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
  have hgm : Measurable g :=
    hrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  obtain ⟨hg, hb, hs⟩ := fp81s21_MomentRep_time_product E P Q q M a H hrep ha hH
  obtain ⟨U, hUm, hUL, hUeq, hUin⟩ := fp81s21_time_section_exists P H g hgm hg
  refine ⟨U, hUm, hUL, hUin.trans_le hb, ?_⟩
  filter_upwards [hs, hUeq] with ω hω heq
  exact ⟨hω, heq⟩

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_TimeL2Rep
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_time_section
