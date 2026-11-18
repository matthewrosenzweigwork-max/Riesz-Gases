import HRS.MS.R2WinOrbNLAux1
import HRS.MS.MovThermAux1

/-!
# S11.6 packet C01 (`R26-T8B.C01`): one S6.3 tuple giving class existence at every smaller radius

Prefix `s116_`, namespace `HRS.MS.S116`.  `s116_class_radii`: constants `ε₀, c₁, C₁` chosen before the thermal reference such that
`R2ClassExists d 0 a β εstar c₁ C₁` holds for every `0 < εstar ≤ ε₀`.  The thermal reference is unique (`mv0_rho_eq`), so the tuple of the
S6.3 conclusion at one reference serves for all of them; for every `εstar` the actual conclusion is reapplied
(`s103n_resulting_of_conclusion`), so no monotonicity of `R2ClassExists` in `εstar` is claimed.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S116

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrbNL

theorem s116_class_radii {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∃ ε₀ c₁ C₁ : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 < C₁ ∧
      ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₀ → R2ClassExists d 0 a β εstar c₁ C₁ := by
  by_cases hex : ∃ ρ, IsThermalEquilibrium d 0 a β ρ
  swap
  · exact ⟨1, 1, 1, one_pos, one_pos, one_pos, fun εstar _ _ ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hex⟩
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have H : Mov2dTh d 0 β a ρ₀ := ⟨hd, le_rfl, hsd, hβ, ha, hρ₀⟩
  have hj' : 1 ≤ 100 * d + 1000 := by omega
  have hm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  obtain ⟨εs', r, c', C', hε', hr, hc', hC', -, hconc⟩ :=
    s67bd_shrink_nonlinear H (100 * d + 1000) (102 * d + 1020) hj' hm 1 one_pos
  refine ⟨εs', c', C', hε', hc', hC', fun εstar hεstar hle ρβ hρβ ε ψ hψ => ?_⟩
  have heq : ρβ = ρ₀ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd le_rfl hsd ha hβ hρβ, HRS.MS.Mov0.mv0_rho_eq hd le_rfl hsd ha hβ hρ₀]
  subst heq
  exact s103n_resulting_of_conclusion H hc' hC' hconc hle hψ

end HRS.MS.S116

end
