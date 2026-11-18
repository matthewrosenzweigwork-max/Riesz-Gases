import HRS.MS.S111K4R7
import HRS.MS.S111TermAux2

/-!
# S11.1 / V02 (S11K4): the contract `S111tV02` (Pro `stationary_cubic_reinterpretation`) from `k4_v02`
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.S111K4

open HRS HRS.Whole

variable {d : ℕ}

/-- **Contract V02** (`S111tV02`) for the thermal reference, in the range of the frozen proposition. -/
theorem k4_v02_contract (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (T : ℝ) : HRS.MS.S111T.S111tV02 d s a β T :=
  fun u hu ρ hρ Kb hKb => k4_v02 hd s a β hs0 hs ha hβ T u hu ρ hρ Kb hKb

end HRS.MS.S111K4
