import HRS.MS.S104eC5E
import HRS.MS.S104eC2L

/-!
# S104E route C, packet C5 part F: `A_jc` discharged (`c5_Ajc`) and `c5_hex'` with `C5PHyp` as the only hypothesis

`c5_Ajc`: the `VolHyp` field `A_jc` for `s103bQ d s (ρ ·)` along every resulting solution, from `c2_Q_jc` (C2) with `Aρ` from `c5_rho_unif` and the uniform time continuity `c5_rho_cont`.
`c5_hex'`: `S104eHex d s a β ρβ ε* c₁ C₁` for every `ε*, c₁, C₁` from `hP : ∀ H ≥ 0, C5PHyp d a β⁻¹ 2 η H` alone (packet C1).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb HRS.MS.Ul HRS.MS.S104b

variable {d : ℕ}

theorem c5_Ajc (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ)
    {η : ℝ} (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) (H : ℝ) :
    C5Ajc d s 2 η H ρ := by
  intro t ht B G hG hGc i hi
  set Lnat : ℕ := d + 2 + ⌈s⌉₊ + 5 with hLnat
  have hL : (d : ℝ) + ((2 : ℕ) : ℝ) + s + 4 < (Lnat : ℝ) := by
    have : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    rw [hLnat]; push_cast; linarith
  obtain ⟨Aρ, hA0, hρU⟩ := c5_rho_unif hd hs0 hsd ha hβ εstar c₁ C₁ (2 + 3) Lnat (by omega) hρβ hres
  have hρc := c5_rho_cont hd hs0 hsd ha hβ εstar c₁ C₁ (2 + 3) Lnat (by omega) hρβ hres t
  exact c2_Q_jc hd hs0 hsd 2 hη0 hη1 hL hA0 (fun v hv => hρU v hv.1) hρc
    (holB_nonneg (hG t ⟨ht.1, le_rfl⟩)) hG hGc i hi

theorem c5_hex' (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ)
    {η : ℝ} (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1)
    (hP : ∀ H : ℝ, 0 ≤ H → Nonempty (C5PHyp d a β⁻¹ 2 η H)) :
    S104eHex d s a β ρβ εstar c₁ C₁ :=
  c5_hex hd hs0 hsd ha hβ εstar c₁ C₁ hρβ hη0 hη1 hP
    (fun _ _ _ _ hres H _ => c5_Ajc hd hs0 hsd ha hβ εstar c₁ C₁ hρβ hres hη0 hη1 H)

end HRS.MS.S104e.C
