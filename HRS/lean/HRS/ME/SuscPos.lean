import HRS.Equilibrium.StaticLimits
import HRS.Sections.Q41Aux14
import HRS.Kernel.Riesz
import HRS.Energy.StaticLimitGauss

/-!
# HRS.ME.SuscPos: positivity of the susceptibility variance (Example 5.11, `v > 0`)

Packet A of the Example 5.11 worker plan.  For a smooth nonconstant `ψ` and a thermal density `ρ`
(`IsThermalDensity`, with smooth potential `V`), `susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ > 0`.

Route: `HRS.susceptibilityCov_bounds` (Kernel/Riesz.lean, Response section) gives
`c ‖P_μ ψ‖²_{L²(μ)} ≤ C_{β,μ}(ψ,ψ)` with `c > 0`; and `‖P_μ ψ‖²_{L²(μ)} = ∫ ρ (P_μ ψ)² dx > 0`
because `ρ` is continuous and strictly positive (`HRS.Q41.q41_thermal_pos_cont`) and
`P_μ ψ` is continuous and not identically zero (`ψ` is nonconstant).
-/

open MeasureTheory Filter Topology ProbabilityTheory

noncomputable section

namespace HRS.ME.SuscPos

variable {d : ℕ}

theorem susc_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (hnc : ∃ x y, ψ x ≠ ψ y) :
    0 < susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hVc : Continuous V := StaticLimitAux.continuous_of_smooth hV
  obtain ⟨hpos, hcont⟩ := HRS.Q41.q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ
  have hprob : IsProbDensity ρ := hρ.1
  have := isProb_withDensityReal hprob
  -- bounds on the density
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  have hΛ : ∀ x, ρ x ≤ max M 0 := fun x =>
    le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using hM x (Set.mem_univ x))
      (le_max_left _ _))
  -- lower bound of the susceptibility by the L²(μ) norm of P_μ ψ
  obtain ⟨c, C, hc, H⟩ := HRS.susceptibilityCov_bounds hd hs0 hsd ρ hprob (max M 0) hΛ β hβ.le
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have hψL : MemLp ψ 2 (withDensityReal ρ) := by
    obtain ⟨M', hM'⟩ := isCompact_univ.exists_bound_of_continuousOn hψc.continuousOn
    exact MemLp.of_bound hψc.aestronglyMeasurable M'
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hM' x (Set.mem_univ x))
  have hlow := (H ψ hψL).1
  -- the projected function is continuous and not identically zero
  set g : Torus d → ℝ := projMean (withDensityReal ρ) ψ with hg
  have hgc : Continuous g := by
    have : g = fun x => ψ x - pair (withDensityReal ρ) ψ := rfl
    rw [this]
    exact hψc.sub continuous_const
  obtain ⟨x, y, hxy⟩ := hnc
  have hx0 : ∃ x0, g x0 ≠ 0 := by
    by_contra hcon
    have hall : ∀ z, g z = 0 := fun z => by
      by_contra hz
      exact hcon ⟨z, hz⟩
    apply hxy
    have h1 : g x = g y := by rw [hall x, hall y]
    have h2 : g x = ψ x - pair (withDensityReal ρ) ψ := rfl
    have h3 : g y = ψ y - pair (withDensityReal ρ) ψ := rfl
    linarith
  obtain ⟨x0, hx0⟩ := hx0
  -- the L²(μ) norm is positive
  have hL : 0 < l2Inner (withDensityReal ρ) g g := by
    unfold l2Inner
    rw [integral_withDensityReal_eq ρ hprob.measurable (fun z => hprob.nonneg z)]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (f := fun z => ρ z * (g z * g z)) (x := x0) (hcont.mul (hgc.mul hgc))
      (HasCompactSupport.of_compactSpace _) ?_ ?_
    · intro z
      exact mul_nonneg (hprob.nonneg z) (mul_self_nonneg _)
    · exact mul_ne_zero (hpos x0).ne' (mul_self_ne_zero.mpr hx0)
  have hcL : 0 < c * l2Inner (withDensityReal ρ) g g := mul_pos hc hL
  exact lt_of_lt_of_le hcL hlow

end HRS.ME.SuscPos

end
