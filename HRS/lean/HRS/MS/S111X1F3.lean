import HRS.MS.S111X1F2
import HRS.MS.S111X1Aux9

/-!
# S11.1 X1: the analytic input from the thermal model, up to the existence of classical solutions

`x1Input_of_exist`: `X1Input` for the thermal model, conditional only on the existence of classical adjoint solutions
for oscillator test functions (`hexist`).  Uniqueness, linear combinations, the energy estimate and the thermal facts are proved.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- Existence of classical adjoint solutions for the oscillator test functions (the one open input). -/
def ClassicalExist (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ →
    ∃ f, IsClassicalAdjointW (x1C d s a β ρ) t ψ f

theorem x1Input_of_exist (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (γ : ℝ) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ)
    (hex : ClassicalExist d s a β ρ) : X1Input d s a β γ ρ := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, E, hρ1⟩ := enData_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨B, hBdef, hGap, hcb⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρ
  exact
    { meas := E.K.meas
      pos := hGap.pos
      int := E.K.int
      bdd := ⟨M, E.K.bdd⟩
      exist := hex
      uniq := uniq_of_thermal hd hs0 hs ha hβ hρ
      comb := comb_of_thermal hd hs0 hs ha hβ hρ
      energy := fun t ht => by
        obtain ⟨c, hc, h⟩ := energy_field E hρ1 ht
        exact ⟨c, hc, fun ψ _ f hf => h ψ f hf⟩ }

theorem r2_cross_density_exists_of_exist
    (hex : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < (d : ℝ) / 2 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → ClassicalExist d s a β ρ) :
    type_of% @HRS.Whole.r2_cross_density_exists := by
  refine HRS.MS.S111BD.r2_cross_density_exists_of_core ?_
  intro d hd s hs0 hs a β γ ha hβ hγ hγs ρ hρ
  exact x1_core_of_input (x1Input_of_exist hd hs0 hs ha hβ γ hρ (hex d hd s hs0 hs a β ha hβ ρ hρ))

end HRS.MS.S111X1
