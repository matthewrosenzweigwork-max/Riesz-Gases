import HRS.MS.GenPathAux29

/-!
# S5.6 packet P4b: continuity of `Ξ_N` in the configuration and in time
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_coord_sub {m : ℝ} (u v : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (u - v) α = OscDual.coord u α - OscDual.coord v α := by
  rw [sub_eq_add_neg, OscDual.coord_add, show -v = (-1 : ℝ) • v by simp, OscDual.coord_smul]
  ring

/-- Continuity into `B_m` from coordinatewise continuity and a summable square bound. -/
theorem s56_osc_cont_of_coord {m : ℝ} {Y : Type*} [TopologicalSpace Y] (u : Y → OscDual d m)
    (B : MultiIndex d → ℝ) (hB : Summable fun α => B α ^ 2)
    (hc : ∀ α, Continuous fun y => OscDual.coord (u y) α)
    (hb : ∀ y α, |OscDual.coord (u y) α| ≤ B α) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro y0
  unfold ContinuousAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun y => ∑' α, (OscDual.coord (u y - u y0) α) ^ 2) (𝓝 y0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 y0)
      (f := fun y α => (OscDual.coord (u y - u y0) α) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun α => 4 * B α ^ 2) (hB.mul_left 4)
      (fun α => ?_) (Filter.Eventually.of_forall fun y α => ?_)
    · simpa using this
    · have h1 : Continuous fun y => (OscDual.coord (u y - u y0) α) ^ 2 := by
        simp_rw [s56_coord_sub]
        exact ((hc α).sub continuous_const).pow 2
      have e0 : (OscDual.coord (u y0 - u y0) α) ^ 2 = 0 := by rw [s56_coord_sub]; ring
      have := h1.tendsto y0
      rw [e0] at this
      exact this
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), s56_coord_sub]
      have h1 := hb y α
      have h2 := hb y0 α
      have : |OscDual.coord (u y) α - OscDual.coord (u y0) α| ≤ 2 * B α :=
        (abs_sub _ _).trans (by linarith)
      nlinarith [abs_nonneg (OscDual.coord (u y) α - OscDual.coord (u y0) α), sq_abs (OscDual.coord (u y) α - OscDual.coord (u y0) α)]
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at this
  exact this.congr fun y => (OscDual.norm_eq_coord _).symm

end HRS.MS.GenPath
