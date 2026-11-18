import HRS.Main.ThermLinPlan2

/-!
# THERMLIN2, packet Ba, part 1: Z0 (`tl2_isStationary_finite`), A1 (`tl2_Wpkg`), Z3 (`tl2_Vev_decay`)

Proofs of the plan statements of `HRS.Main.ThermLinPlan2` with the statements copied verbatim.
No plan statement is used as a black box.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- (Z0) proof: restriction of the hypotheses of `IsStationaryGaussianField` from `[0,∞)` to `[0,T']`. -/
theorem tl2_isStationary_finite_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ} (m T' : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m)
    (hZ : IsStationaryGaussianField P S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) : Tl2StatFdd S ρβ m T' P Z := by
  refine ⟨hZ.meas, ?_, fun p τ φ hτ hφ => hZ.gaussian p τ φ (fun a => (hτ a).1) hφ⟩
  filter_upwards [hZ.cont] with ω hω
  exact hω.mono (fun t ht => ht.1)

/-- A1 proof: `t25p_ev_pkg` for the constant path `thermlin_stationary_traj`.  -/
theorem tl2_Wpkg_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) :
    ∃ Cw cw : ℝ, 0 < Cw ∧ 0 < cw ∧ ∃ Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution S.dyn (fun _ => ρβ) m Wev ∧
      ∀ T : ℝ, 0 < T → ∃ Cmax : ℝ, 0 ≤ Cmax ∧ T25Ev m Cw cw T Cmax Wev :=
  t25p_ev_pkg S.hd (HRS.ThermLin.thermlin_stationary_traj S h) m

/-- (Z3) proof: any dual evolution along `S.ρ` agrees on the simplex with the one of `adjk_evolution_along_trajectory`
(`t25p_dual_unique`). -/
theorem tl2_Vev_decay_proof (S : HRS.Main.PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ K₀ c₀ : ℝ, 0 ≤ K₀ ∧ 0 < c₀ ∧ ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution S.dyn S.ρ m Vev → (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') →
      ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K₀ * Real.exp (-c₀ * (t - u)) := by
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ :=
    adjk_evolution_along_trajectory S.hd (HRS.T25.t25_traj S) m
  refine ⟨Cr, cr, hCr.le, hcr, fun Vev hdual _ u t hu hut => ?_⟩
  rw [t25p_dual_unique hdual hdualA hu hut]
  exact hdecA u t hu hut

example := (@tl2_isStationary_finite_proof : type_of% @tl2_isStationary_finite)
example := (@tl2_Wpkg_proof : type_of% @tl2_Wpkg)
example := (@tl2_Vev_decay_proof : type_of% @tl2_Vev_decay)

end HRS.ThermLin.Plan2
