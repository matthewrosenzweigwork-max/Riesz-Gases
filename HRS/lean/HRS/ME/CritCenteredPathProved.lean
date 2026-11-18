import HRS.ME.CritFinalUnif
import HRS.ME.NfUPU13b

/-!
# Chunk E, row 2.10: the frozen `critical_centered_path`, proved

`HRS.ME.CritFinalUnif.critical_centered_path_of_modePackage` reduces the frozen clause (constant uniform in `β ∈ [βm, βp]`) to the
uniform mode package.  `HRS.ME.unifModePackage` (`HRS/ME/NfUPU13b.lean`) proves it, from the uniform pair-Poisson theorem
(`pair_poisson_unif_thermal`) and the uniform normal form (`normal_form_unif_thermal`).
-/

namespace HRS.ME.CritFinalUnif

/-- The frozen `HRS.Main.critical_centered_path`, with no hypothesis. -/
theorem critical_centered_path_proved {d : ℕ} : type_of% (@HRS.Main.critical_centered_path d) :=
  critical_centered_path_of_modePackage
    (fun hd V hV βm βp hβm hββ => HRS.ME.unifModePackage hd V hV βm βp hβm hββ)

end HRS.ME.CritFinalUnif
