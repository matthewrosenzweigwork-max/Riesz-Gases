import HRS.ME.Marginal

/-! Tie of the proved `criticalBias_ne_zero_of_nonneg` to the repaired frozen statement `HRS.Main.criticalBias_ne_zero`
(Proposition 2.10, `M:H:prop:critical`, TeX L1051-1052; repair ME-R4: `0 ≤ m`). -/

namespace HRS.ME.Marginal

open HRS HRS.Main

theorem criticalBias_ne_zero_proof {d : ℕ} (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hnc : ∃ x y, ρ x ≠ ρ y) (m : ℝ) (hm : 0 ≤ m) :
    criticalBias d ((d : ℝ) / 2) β m ρ ≠ 0 :=
  criticalBias_ne_zero_of_nonneg hd β hβ hρ hnc m hm

example := (@criticalBias_ne_zero_proof : type_of% @HRS.Main.criticalBias_ne_zero)

end HRS.ME.Marginal
