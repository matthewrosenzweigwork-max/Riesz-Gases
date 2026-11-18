import HRS.MS.S88BDF01
import HRS.MS.S88BDF02
import HRS.Whole.CriticalNoise

/-!
# S8.8 final tie: `s88_initial_decay : type_of% @HRS.Whole.return_map_initial_decay`

The constants `c` and `b` are chosen once by `s88_orbit_envelopes` (before `ρ`, `u`, `N` and the fields), the common
constant is `CT = s88Constant T Cin b`, and the two clauses are the particle (F01) and the rational-time Gaussian (F02)
decay bounds.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

theorem s88_initial_decay : type_of% @HRS.Whole.return_map_initial_decay := by
  intro d hd a β ha hβ m hm T hT Cin
  obtain ⟨c, b, hc, hb, hsum, hall⟩ := s88_orbit_envelopes hd a β ha hβ m hm
  refine ⟨s88Constant T Cin b, c, hc, ?_⟩
  intro ρ hρ
  obtain ⟨hreg, henv⟩ := hall ρ hρ
  refine ⟨hreg.classical, ?_⟩
  intro u hu
  constructor
  · intro N hN Ω mΩ P hP X hlaw hvar
    exact s88_particle_decay hd a β ha hβ m ρ hρ c b hb hsum hreg henv
      T Cin u hT hu N hN P X hlaw hvar
  · intro Ω mΩ P hP η hη
    exact s88_gaussian_decay hd a β ha hβ m ρ hρ c b hb hsum hreg henv
      T Cin u hT hu P η hη

example := (@s88_initial_decay : type_of% @HRS.Whole.return_map_initial_decay)

end HRS.MS.S88Breakdown
