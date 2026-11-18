import HRS.MD.EQBurnBurnMain
import HRS.MD.EQBurnZero
import HRS.MD.EQEvoFinal
import HRS.MD.EQBurnDefs

/-!
# Packet EQ-BURN P8 (wiring, EQP8): `eq_burnin_proof`

Relocated proof of the frozen statement `HRS.MD.EQ29.eq_burnin` (the tie is `HRS/MD/EQBurnWireTie.lean`).  The uniform evolution estimate
`HRS.MD.EQEvoFinal.eq_evolution_uniform_proof` (P7) is converted into the `EvoPkg` package (`eqbw_evoPkg`), then
`eq_burnin_of_evo_proof` (P4, `T > 0`) and `eq_burnin_zero_proof` (P5, `T = 0`, window length `1`) give `BurninConcl`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnWire

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQBurn

variable {d : ℕ}

/-- The uniform evolution output at window length `T ≥ 0` (P7) gives the evolution package `EvoPkg` at window length `T`.
The measurable maximal estimate `MaxWindowsM` follows from `MaxWindows` (a measurable `Z` is a.e. measurable). -/
theorem eqbw_evoPkg {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ EvoPkg d s hs0 hsd V βm βp hβm m K c T Cmax := by
  obtain ⟨K, c, Cmax, hK, hc, hCmax, h⟩ :=
    HRS.MD.EQEvoFinal.eq_evolution_uniform_proof hd hs0 hsd V hV βm βp hβm hββ m T hT
  refine ⟨K, c, Cmax, hK, hc, hCmax, ?_⟩
  intro β hβ ρβ hρ
  obtain ⟨Vev, hdual, hplain, hdec, hmax, hconv⟩ := h β hβ ρβ hρ
  refine ⟨Vev, ⟨hplain, hdec, ?_, ?_⟩, hdual⟩
  · intro Ω mΩ P _ ℱ a ha M Sg hM Z hZS hZc hZm
    exact hmax Ω P ℱ a ha M Sg hM Z (fun t _ => (hZm t).aemeasurable) hZS hZc
  · intro T' hT' Ω mΩ P _ ℱ M Sg hM
    exact hconv T' hT'.le Ω P ℱ M Sg hM

/-- (P8.) `eq_burnin` (frozen as `HRS.MD.EQ29.eq_burnin`, `HRS/MD/EQ29Spec.lean`), stated with the conclusion `BurninConcl`,
which is definitionally the conclusion of the frozen statement. -/
theorem eq_burnin_proof {d : ℕ} : ∀ (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 ≤ T),
    BurninConcl d s hs0 hsd V βm βp hβm m T := by
  intro hd s hs0 hsd V hV βm βp hβm hββ m hm T hT
  rcases hT.lt_or_eq with hTpos | hT0
  · obtain ⟨K, c, Cmax, hK, hc, hCmax, hP⟩ :=
      eqbw_evoPkg (d := d) hd hs0 hsd V hV βm βp hβm hββ m T hT
    exact HRS.MD.EQBurnBurn.eq_burnin_of_evo_proof hd hs0 hsd V hV βm βp hβm hββ m hm T hTpos
      K c Cmax hK hc hCmax hP
  · subst hT0
    obtain ⟨K, c, Cmax, hK, hc, hCmax, hP⟩ :=
      eqbw_evoPkg (d := d) hd hs0 hsd V hV βm βp hβm hββ m 1 zero_le_one
    exact HRS.MD.EQBurnZero.eq_burnin_zero_proof hd hs0 hsd V hV βm βp hβm hββ m hm K c Cmax hK hc hCmax hP

end HRS.MD.EQBurnWire

end
