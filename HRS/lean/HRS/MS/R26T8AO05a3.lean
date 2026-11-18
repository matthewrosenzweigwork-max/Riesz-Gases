import HRS.MS.R26T8AO05a2
import HRS.MP.SelfSimP4Reg

/-!
# S8.2 observed-time layer, packet T8A.O05a (helper 3): progressivity for the shifted filtration

A process progressive for `ℱ` whose time-zero value is `ℱ 0`-measurable is progressive for the negative-time shift
`p4r_shiftFil ℱ`, because it is the constant `X 0` at negative times.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.MP.SelfSimP4Impl

theorem r26t8a_o05a3_prog_shift {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → β}
    (hprog : IsProgressive ℱ (ofNNRealTime X)) (had0 : Measurable[ℱ 0] (X 0)) :
    IsProgressive (p4r_shiftFil ℱ) (ofNNRealTime X) := by
  intro i
  by_cases hi : 0 ≤ i
  · have : p4r_shiftFil ℱ i = ℱ i := by rw [p4r_shiftFil_apply, max_eq_left hi]
    rw [this]
    exact hprog i
  · have hi' : i ≤ 0 := (not_le.1 hi).le
    have e : (fun p : Set.Iic i × Ω => ofNNRealTime X (p.1 : ℝ) p.2) = fun p => X 0 p.2 := by
      funext p
      have h1 : (p.1 : ℝ) ≤ i := p.1.2
      simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos (h1.trans hi')]
    have hsh : p4r_shiftFil ℱ i = ℱ 0 := by rw [p4r_shiftFil_apply, max_eq_right hi']
    rw [e, hsh]
    exact had0.comp (@measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ 0))

end HRS.MS.R26T8A

end
