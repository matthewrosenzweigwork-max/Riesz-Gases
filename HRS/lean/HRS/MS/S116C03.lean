import HRS.MS.S116C01
import HRS.MS.S105rTie

/-!
# S11.6 packet C03 (`R26-T8B.C03`): a nonempty class compatible with native terminal regularity

Prefix `s116_`, namespace `HRS.MS.S116`.  Given `S105rTermReg` (supplied natively by `s104j_termReg s104e_hexSmall`), the tuple of `s116_class_radii` and the radius `εn` of
`S105rTermReg` for the same `c₁, C₁` give `εstar = min ε₀ εn`: class existence and `S104bTermRegGen` for every thermal reference.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_class_with_reg
    (hTR : HRS.MS.S105r.S105rTermReg)
    {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∃ εstar c₁ C₁ : ℝ, 0 < εstar ∧ 0 < c₁ ∧ 0 < C₁ ∧
      R2ClassExists d 0 a β εstar c₁ C₁ ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d 0 a β ρβ →
        HRS.MS.R2WinErr.S104bTermRegGen d 0 a β ρβ εstar c₁ C₁ := by
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₀, c₁, C₁, hε₀, hc₁, hC₁, hcl⟩ := s116_class_radii hd a β ha hβ
  obtain ⟨εn, hεn, hreg⟩ := hTR hd 0 a β c₁ C₁ le_rfl hsd ha hβ
  have hpos : 0 < min ε₀ εn := lt_min hε₀ hεn
  exact ⟨min ε₀ εn, c₁, C₁, hpos, hc₁, hC₁, hcl _ hpos (min_le_left _ _),
    fun ρβ hρβ => hreg _ (min_le_right _ _) ρβ hρβ⟩

end HRS.MS.S116

end
