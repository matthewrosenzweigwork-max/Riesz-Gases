import HRS.MS.R2MtAux1

/-!
# S11.6 packet N04 (`R26-T8B.N04`): uniform positive endpoint of the logarithmic pressure

Prefix `s116_`, namespace `HRS.MS.S116`.  For `b > 0` and a round-2 class `IsRound2Density d 0 M L`: `GibbsWellDefined` and
`|log K_{N,b}| ≤ B` with `B` independent of `ρ` and `N ≥ 2` (the `s = 0` case of `s92_normalizer_bounds`, `pairNormalizer = gibbsNormalizer` by `rfl`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_positive_endpoint {d : ℕ} (hd : 2 ≤ d) (M L b : ℝ) (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : Euc d → ℝ, IsRound2Density d 0 M L ρ →
      ∀ N : ℕ, 2 ≤ N →
        GibbsWellDefined (fun x y : Euc d => rieszKernel d 0 (x - y)) N b
          (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N b (HRS.Whole.withDensityReal ρ))| ≤ B := by
  have hd0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    linarith
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd (s := 0) le_rfl hd0 M L b (2 * b) hb (by linarith)
  exact ⟨C, hC0, fun ρ hρ N hN => hC ρ hρ N hN b ⟨le_rfl, by linarith⟩⟩

end HRS.MS.S116

end
