import HRS.MS.S104eEx1

/-!
# S11.6 packet P04 (`R26-T8B.P04`): integrable first-jet decay of the nonlinear coefficient

Prefix `s116_`, namespace `HRS.MS.S116`.  Along a resulting solution `ρ` the densities `ρ t`, `t ≥ 0`, satisfy `U2Dec 1 (d+1) A (ρ t)` with a common `A ≥ 0`
(common Gaussian bound of the first jets `s104e_gauss_rho`, then `s104e_u2dec_of_gauss`).
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_rho_decay {d : ℕ} (hd : 2 ≤ d) {a β εstar c₁ C₁ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d 0 a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ}
    (hres : IsResultingSolution d 0 a β ρβ εstar ε ψ c₁ C₁ ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 ≤ t → U2Dec 1 ((d : ℝ) + 1) A (ρ t) := by
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨c, K, hc, hK, hbd⟩ := HRS.MS.S104e.s104e_gauss_rho hd (s := 0) le_rfl hsd ha hβ εstar c₁ C₁ 1
    (by omega) hρβ hres
  obtain ⟨P, hP, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss (d := d) hc 1 (d + 1)
  refine ⟨P * K, mul_nonneg hP hK, fun t ht => ?_⟩
  obtain ⟨hcd, hk⟩ := hbd t ht
  have := hU (ρ t) K hK hcd hk
  simpa using this

end HRS.MS.S116

end
