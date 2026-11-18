import HRS.ME.CritFinal
import HRS.ME.CritUnifMode
import HRS.ME.CritUnifAssembly
import HRS.ME.CritUnifDecay

/-!
# Chunk E, row 2.10 path clause: `critical_centered_path` relative to the two uniform-in-`β` inputs

`critical_centered_path_of_unif`: the frozen `HRS.Main.critical_centered_path` (type taken by `type_of%`) from

* `HRS.ME.Crit.UnifDecay`: the decay of the Fourier coefficients of the equilibrium semigroup
  (`fourier_coeff_decay_proof` with the constants chosen before `β ∈ [βm, βp]`), and
* `HRS.ME.Crit.UnifModePackage`: the mode package (`mode_package_proof` with the constant chosen before `β ∈ [βm, βp]`),

for all data.  Every other constant of the proof of Proposition 4.17 is independent of `β` or depends on it only through `β⁻¹ ≤ βm⁻¹`.
`HRS.ME.Crit.unif_decay` proves `UnifDecay`, so `critical_centered_path_of_modePackage` has the mode package as its only hypothesis;
`UnifModePackage` is not proved uniformly yet (see `docs/MAIN_E_BATCH5.md`).
-/

namespace HRS.ME.CritFinalUnif

theorem critical_centered_path_of_unif {d : ℕ}
    (hdec : ∀ (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
      (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp), HRS.ME.Crit.UnifDecay d hs0 hsd V βm βp hβm)
    (hpkg : ∀ (hd : 2 ≤ d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp),
      HRS.ME.Crit.UnifModePackage d hd V hV βm βp hβm) :
    type_of% (@HRS.Main.critical_centered_path d) :=
  HRS.ME.CritFinal.critical_centered_path_of_uniform417
    (fun hd hs0 hsd V hV βm βp hβm hββ m hm T hT =>
      HRS.ME.Crit.uniform417_of_unif hd hs0 hsd V hV βm βp hβm m hm T hT (hdec hd hs0 hsd V hV βm βp hβm hββ)
        (fun c hc => HRS.ME.Crit.unif_mode_forcing hd hs0 hsd V hV βm βp hβm (hpkg hd V hV βm βp hβm hββ) c hc T hT.le))

/-- The frozen `critical_centered_path` from the uniform mode package alone. -/
theorem critical_centered_path_of_modePackage {d : ℕ}
    (hpkg : ∀ (hd : 2 ≤ d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp),
      HRS.ME.Crit.UnifModePackage d hd V hV βm βp hβm) :
    type_of% (@HRS.Main.critical_centered_path d) :=
  critical_centered_path_of_unif
    (fun hd hs0 hsd V hV βm βp hβm hββ => HRS.ME.Crit.unif_decay hd hs0 hsd V hV βm βp hβm hββ) hpkg

end HRS.ME.CritFinalUnif
