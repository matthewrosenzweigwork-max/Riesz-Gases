import HRS.MS.MovEntAux5

/-!
# S6.6, packet P1: the completion constant (first conjunct of the frozen statement)

`s66_clause0`: there is `C₀ ≥ 1` with `0 ≤ F_N(X, μ) + o_N` for every `N ≥ 2`, every collision-free `X` and every density of the S3.1 class
with `‖ρ‖_∞ ≤ M` (`M ≥ 1`) and, at `s = 0`, `∫ log(2+|x|) dμ < ∞` (from `completionNonnegRd_exists` and `oNΛ_le_oN`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_oN_mono {s : ℝ} {C₀ C₀' : ℝ} (h : C₀' ≤ C₀) {N : ℕ} (hN : 1 ≤ N) :
    oN d s C₀' N ≤ oN d s C₀ N := by
  unfold oN
  have hx : 0 ≤ (N : ℝ) ^ (s / d - 1) :=
    Real.rpow_nonneg (by exact_mod_cast Nat.zero_le N) _
  nlinarith

theorem s66_clause0 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (wd ρ)) →
      ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (wd ρ) + oN d s C₀ N := by
  obtain ⟨C₀', hC₀'0, hall⟩ := HRS.MH.CoercLower.completionNonnegRd_exists hd hs0 hsd
  have hcn := hall C₀' le_rfl
  obtain ⟨-, C₀'', hC₀''0, hle⟩ := HRS.oNΛ_le_oN hd hs0 hsd C₀' hC₀'0 M hM
  refine ⟨max 1 C₀'', le_max_left _ _, fun N hN ρ hρ hρM hlog X hX => ?_⟩
  have h1 := hcn.2 M hM N hN ρ hρ hρM hlog X hX
  have h2 := hle N hN
  have h3 := s66_oN_mono (d := d) (s := s) (le_max_right 1 C₀'') (N := N) (by omega)
  linarith

end HRS.MS.MovEnt

end
