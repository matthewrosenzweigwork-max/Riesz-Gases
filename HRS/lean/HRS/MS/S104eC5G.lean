import HRS.MS.S104eC5F
import HRS.MS.S104eC1M

/-!
# S104E route C, packet C5 part G: the unconditional existence `S104eHex`

`c5_hex_final`: for `2 ≤ d`, `0 ≤ s < d`, `a, β > 0`, every thermal equilibrium `ρβ` and every `ε*, c₁, C₁`, every resulting solution has, for every Hermite datum `φ_α` and
every terminal time `t ≥ 0`, a classical adjoint solution (`S104eHex`).  The semigroup-side fields come from `c1_P_fields` (C1), the perturbation side from C2, the Picard
solution from C3 and the classical clauses from C4; `ε*` need not be small.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.S104b

variable {d : ℕ}

theorem c5_hex_final (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) :
    S104eHex d s a β ρβ εstar c₁ C₁ := by
  set η : ℝ := (max 0 (s - d + 1) + 1) / 2 with hη
  have hm : max 0 (s - d + 1) < 1 := max_lt (by norm_num) (by linarith)
  have hη0 : max 0 (s - d + 1) < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  refine c5_hex' hd hs0 hsd ha hβ εstar c₁ C₁ hρβ hη0 hη1 (fun H hH => ?_)
  have h := c1_P_fields (d := d) a β⁻¹ ha (inv_pos.2 hβ) hηp hη1 2 H
  obtain ⟨CP, hCP1, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨⟨CP, hCP1, h1, h2, h3, h4, h5, h6, h7⟩⟩

end HRS.MS.S104e.C
