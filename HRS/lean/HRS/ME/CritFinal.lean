import HRS.ME.CritBurnin
import HRS.ME.CritPaths
import HRS.ME.CritForcingBridge

/-!
# Chunk E, row 2.10 path clause: `critical_centered_path` relative to the uniform Proposition 4.17

`critical_centered_path_of_uniform417`: the frozen `HRS.Main.critical_centered_path` (type taken by `type_of%`, so the tie holds by
construction) from `HRS.ME.Crit.Uniform417` for all data, i.e. Proposition 4.17 on the finite horizon with the constant chosen
before `β ∈ [βm, βp]`.  Proved sorry-free from `crit_burnin_of_evo_proof` (A4), `crit_forcing_of_uniform417_proof` (B1) and
`crit_paths_of_burnin` (A5).  `Uniform417` itself is not proved (see `docs/MAIN_E_CRIT_PLAN.md`).
-/

namespace HRS.ME.CritFinal

theorem critical_centered_path_of_uniform417 {d : ℕ}
    (hu : ∀ (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
      (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
      (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T),
      HRS.ME.Crit.Uniform417 d hs0 hsd V βm βp hβm m T) :
    type_of% (@HRS.Main.critical_centered_path d) :=
  HRS.ME.CritPaths.crit_paths_of_burnin (@HRS.ME.CritBurnin.crit_burnin_of_evo_proof d)
    (fun hd hs0 hsd V hV βm βp hβm hββ m hm T hT =>
      HRS.ME.CritForcingBridge.crit_forcing_of_uniform417_proof hd hs0 hsd V hV βm βp hβm hββ m T hT
        (hu hd hs0 hsd V hV βm βp hβm hββ m hm T hT))

end HRS.ME.CritFinal
