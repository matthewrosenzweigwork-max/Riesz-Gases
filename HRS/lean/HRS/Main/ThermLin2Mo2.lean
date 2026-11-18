import HRS.Main.ThermLinPlan2

/-!
# THERMLIN2 Mo2: `tl2_rho_sup_decay` (C2), sup-norm decay of `ρ^r - ρβ`

From `thermlin_rho_decay` at the level `r₀ = d/2 + 1` and the sup bound `wire_sup_le`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- C2 (proof). -/
theorem tl2_rho_sup_decay_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : Torus d, |S.ρ r x - ρβ x| ≤ C * Real.exp (-κ * r) := by
  obtain ⟨hsm, -⟩ := HRS.ThermLin.thermlin_thermal_smooth_pos S h
  set r₀ : ℝ := (d : ℝ) / 2 + 1 with hr₀
  have hr₀0 : 0 ≤ r₀ := by positivity
  have hr₀d : (d : ℝ) / 2 < r₀ := by linarith
  obtain ⟨K, ρc, C, c, hC, hc, -, hρ, hdec⟩ := HRS.ThermLin.thermlin_rho_decay S h r₀ hr₀0
  obtain ⟨A, hA0, hA⟩ := PDE.MFAdjoint.wire_sup_le (d := d) r₀ hr₀d
  obtain ⟨L, hL0, hL⟩ := PDE.MFApriori.Aux.exists_l1_le (d := d) r₀ hr₀d
  have hβm : PDE.MemHs r₀ (PDE.coeffOf ρβ) := PDE.MFSemigroup.memHs_of_isSmooth hsm r₀
  have hβs : Summable fun k => ‖PDE.coeffOf ρβ k‖ := (hL _ hβm).1
  have hcont : Continuous ρβ := HRS.StaticLimitAux.continuous_of_smooth hsm
  refine ⟨A * C, c, by positivity, hc, fun r hr x => ?_⟩
  obtain ⟨hmem, hn⟩ := hdec r hr
  have hcs : Summable fun k => ‖(ρc r - PDE.coeffOf ρβ) k‖ := (hL _ hmem).1
  have hρs : Summable fun k => ‖ρc r k‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hcs.add hβs)
    have := norm_add_le ((ρc r - PDE.coeffOf ρβ) k) (PDE.coeffOf ρβ k)
    simpa using this
  have key : S.ρ r x - ρβ x = PDE.toFun (ρc r - PDE.coeffOf ρβ) x := by
    rw [PDE.MFApriori.Aux.toFun_sub _ _ hρs hβs, PDE.toFun_coeffOf ρβ hcont hβs, ← hρ]
    rfl
  rw [key]
  calc |PDE.toFun (ρc r - PDE.coeffOf ρβ) x| ≤ A * PDE.hsNorm r₀ (ρc r - PDE.coeffOf ρβ) := hA _ hmem x
    _ ≤ A * (C * Real.exp (-c * r)) := mul_le_mul_of_nonneg_left (hn) hA0
    _ = A * C * Real.exp (-c * r) := by ring

example := (@tl2_rho_sup_decay_proof : type_of% @tl2_rho_sup_decay)

end HRS.ThermLin.Plan2
