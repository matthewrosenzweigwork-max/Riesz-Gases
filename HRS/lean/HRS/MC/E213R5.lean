import HRS.MC.E213R4
import HRS.MC.E213N3

/-!
# Packet e213r, part 5: Theorem 2.13 (B3), existence of the future Gaussians of a regime

`e213r_exists_future`: for `R : Regime d`, `m > 3d + 8`, `T > 0` there is `γ : ℝ → Measure (PathSpace d m T)` with
`IsFutureGaussian R.D R.ρ m T u (γ u)` for every `u ∈ [0,T]`.  The regime is converted into the prepared trajectory
`s7fcPrep R` (as in `E213N3`), whose `ρ` agrees with `R.ρ` on `[0,∞)`; `IsFutureGaussian` only sees `ρ` on `[u,T] ⊆ [0,∞)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213R

open HRS HRS.Sec7

variable {d : ℕ}

/-- `IsFutureGaussian` only depends on `ρ` on `[0,∞)` (for `u ≥ 0`). -/
theorem e213r_isFutureGaussian_congr (D : DynData d) {ρ ρ' : ℝ → Torus d → ℝ}
    (hρ : ∀ s : ℝ, 0 ≤ s → ρ s = ρ' s) {m T u : ℝ} (hu : 0 ≤ u) {γ : Measure (PathSpace d m T)}
    (h : IsFutureGaussian D ρ m T u γ) : IsFutureGaussian D ρ' m T u γ := by
  refine ⟨h.1, fun ta tb φa φb hφa hφb hta htb => ?_⟩
  rw [h.2 ta tb φa φb hφa hφb hta htb]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
  rw [HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr D ρ ρ' hρ v ta φa,
    HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr D ρ ρ' hρ v tb φb, hρ v (hu.trans hv.1)]

/-- **Theorem 2.13, B3.**  Existence of the future Gaussian measures `γ_u`, `u ∈ [0,T]`, of a regime. -/
theorem e213r_exists_future (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ γ : ℝ → Measure (PathSpace d m T), ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u) := by
  set S := HRS.MC.Sec7.FCPlan.s7fcPrep R with hS
  have htr : IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ :=
    HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S
  have hdyn : htr.dyn = R.D := HRS.MC.Sec7.S7FCW4.S7FCW4_dyn R
  have hρS : ∀ s : ℝ, 0 ≤ s → S.ρ s = R.ρ s := fun s hs => HRS.MC.Sec7.S7FCW4.S7FCW4_rho_eq R hs
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm' : (d : ℝ) / 2 + 2 < m := by linarith
  obtain ⟨γ, hγ⟩ := e213r_future_exists_traj R.hd htr hm' hT
  refine ⟨γ, fun u hu => ?_⟩
  have h1 := hγ u hu
  rw [hdyn] at h1
  exact e213r_isFutureGaussian_congr R.D hρS hu.1 h1

end HRS.MC.E213R
