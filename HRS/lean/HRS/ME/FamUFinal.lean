import HRS.ME.FamUF8
import HRS.ME.FamUF9
import HRS.ME.FamUF10
import HRS.ME.FamUF11
import HRS.Main.HeadlineEquilibrium

/-!
# Chunk E, packet F12: `critical_centered_path_uniform`

`HRS.ME.FamU.critical_centered_path_uniform_proved` has exactly the type of the frozen
`HRS.Main.critical_centered_path_uniform` (`HRS/Main/HeadlineEquilibrium.lean:193`, taken by `type_of%`, so the tie holds by construction).
Proof: a `PotentialFamilyBounded` family gives `Bf j := Λ_j` with `cbNorm j V ≤ Bf j` for all `V ∈ 𝒱`; the family forms
`unif_decayV` (F9), `unifModePackageFam` (F8), `unif_mode_forcingV` (F10), `uniform417_of_unifV` (F10),
`crit_forcing_of_uniform417_unifV` and `crit_paths_of_burnin_unifV` (F11) then give the constant `C` before `V`, and it is
specialized to each `V ∈ 𝒱`.
-/

namespace HRS.ME.FamU

theorem critical_centered_path_uniform_proved {d : ℕ} :
    type_of% (@HRS.Main.critical_centered_path_uniform d) := by
  intro hd hs0 hsd 𝒱 h𝒱 βm βp hβm hββ m hm T hT
  obtain ⟨hsm, hbd⟩ := h𝒱
  choose Bf hBf using hbd
  have hdec := unif_decayV hd hs0 hsd βm βp hβm hββ Bf
  have hpkg := unifModePackageFam hd βm βp hβm hββ Bf
  have hmode : ∀ c : ℝ, 0 < c → UnifModeForcingFam d hs0 hsd βm βp hβm c T Bf :=
    fun c hc => unif_mode_forcingV hd hs0 hsd βm βp hβm Bf hpkg c hc T hT.le
  have h417 := uniform417_of_unifV hd hs0 hsd βm βp hβm m hm T hT Bf hdec hmode
  have hforce := crit_forcing_of_uniform417_unifV hd hs0 hsd βm βp hβm m T Bf h417
  obtain ⟨C, hC, h⟩ := crit_paths_of_burnin_unifV hd hs0 hsd βm βp hβm hββ m hm T hT Bf hforce
  exact ⟨C, hC, fun V hV => h V (hsm V hV) (fun j => hBf j V hV)⟩

end HRS.ME.FamU
