import HRS.MS.WadAux105

/-!
# S8.3, packet S8F-6: the admissible bounds for all iterated differences (induction on the length)

`s8f_jets`: `∃ lam K ≥ 0` (depending only on `d, a, β, T, M, ρβ, N`) such that for every classical solution `f` of terminal datum `φ` on `[0,t]`,
`0 < t ≤ T`, and every list `ξs` with `|ξs| ≤ N`, `Σ‖ξ_i‖ ≤ 1/8`:
`S84Adm lam t M (Δ_{ξs} f) (K Φ ∏‖ξ_i‖)` and `|Δ_{ξs} f_r(y)| ≤ K Φ ∏‖ξ_i‖ ⟨y⟩^M`, whenever `Φ ≥ 0` dominates the terminal values
(`Wt M (Φ ∏‖ξ_i‖) (Δ_J f_t)` for every small `J`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_jets (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (N : ℕ) :
    ∃ lam K : ℝ, 0 ≤ lam ∧ 0 ≤ K ∧ s8f_Claim a β T M ρβ N lam K (N + 1) := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hg := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨CB, hCB0, hCB⟩ := s84_B_bound hd hg hM
  obtain ⟨lam, K, hlam, hK, hgen⟩ := s8e_apriori_gen (d := d) ha hν hT hM (cB := 2 * CB) (by positivity)
  obtain ⟨C0, c0, hC0, hc0, hGB⟩ := s8f_thermal_GB hd ha hβ hρ (N + 1)
  obtain ⟨Kc, hKc0, hKc⟩ := s8e_B_bound_unif hd (show 0 < c0 / 2 ^ N by positivity) hM
  have key : ∀ m : ℕ, ∃ Kn : ℝ, 0 ≤ Kn ∧ s8f_Claim a β T M ρβ N lam Kn m := by
    intro m
    induction m with
    | zero => exact ⟨0, le_rfl, fun ht htT hf hΦ hdat ξs hξs hlen => absurd hlen (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨Kp, hKp, hprev⟩ := ih
      exact s8f_step hd ha hβ hM N hCB hK hgen hC0 hc0 hGB hKc0 hKc m Kp hKp hprev
  obtain ⟨Kn, hKn, hcl⟩ := key (N + 1)
  exact ⟨lam, Kn, hlam, hKn, hcl⟩

end HRS.MS.Wad
