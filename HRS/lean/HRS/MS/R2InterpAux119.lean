import HRS.MS.R2InterpAux118

/-!
# S10.2 (worker S10R), part 119 (packet M3i): continuity of `B_m`-valued maps with `ℓ²`-dominated, coordinatewise continuous coordinates

Used for `u ↦ V^{t,u}ζ^u` (coordinates `ζ^u(U^{u,t}φ_α)`, dominated by `|M| s57pC c_α`, `c ∈ ℓ²`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m : ℝ}

theorem s102_lp_continuousOn {S : Set ℝ} (a : ℝ → MultiIndex d → ℝ) (hmem : ∀ u, Memℓp (a u) 2)
    (b : MultiIndex d → ℝ) (hb : Summable fun α => b α ^ 2) (hbd : ∀ u ∈ S, ∀ α, |a u α| ≤ b α)
    (hc : ∀ α, ContinuousOn (fun u => a u α) S) :
    ContinuousOn (fun u => (show OscDual d m from (⟨a u, hmem u⟩ : lp (fun _ : MultiIndex d => ℝ) 2))) S := by
  intro u0 hu0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ u, ‖(show OscDual d m from (⟨a u, hmem u⟩ : lp (fun _ : MultiIndex d => ℝ) 2)) -
      (show OscDual d m from (⟨a u0, hmem u0⟩ : lp (fun _ : MultiIndex d => ℝ) 2))‖ =
      Real.sqrt (∑' α : MultiIndex d, (a u α - a u0 α) ^ 2) := by
    intro u
    rw [OscDual.norm_eq_coord]
    congr 1
  have hlim : Tendsto (fun u => ∑' α : MultiIndex d, (a u α - a u0 α) ^ 2) (𝓝[S] u0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[S] u0)
      (f := fun u α => (a u α - a u0 α) ^ 2) (g := fun _ => 0)
      (bound := fun α => 4 * b α ^ 2) (hb.mul_left 4)
      (fun α => by
        have h1 : Tendsto (fun u => a u α) (𝓝[S] u0) (𝓝 (a u0 α)) := hc α u0 hu0
        simpa using (h1.sub_const (a u0 α)).pow 2)
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu α
        have h1 := hbd u hu α
        have h2 := hbd u0 hu0 α
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have : |a u α - a u0 α| ≤ 2 * b α := by
          calc |a u α - a u0 α| ≤ |a u α| + |a u0 α| := abs_sub _ _
            _ ≤ 2 * b α := by linarith
        have h0 : 0 ≤ 2 * b α := (abs_nonneg _).trans this
        nlinarith [sq_abs (a u α - a u0 α), abs_nonneg (a u α - a u0 α)])
    simpa using this
  have hsq : Tendsto (fun u => Real.sqrt (∑' α : MultiIndex d, (a u α - a u0 α) ^ 2)) (𝓝[S] u0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  simpa only [hnorm] using hsq

end HRS.MS.R2Interp

end
