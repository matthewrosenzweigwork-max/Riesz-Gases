import HRS.MS.MovEntAux13
import HRS.MS.MovEntAux9
import HRS.MS.CanThm

/-!
# S6.6, packet P6 (part 8): clause (1) of `mov_entropy` from `SuperDiss d s`

`s66_clause1`: under the dissipation inequality (DISS, the hypothesis `SuperDiss d s` of S.B.1), for the S6.3 class (constants of
`MovNonlinearConclusion` and the S6.4 weighted bounds) there is `C` such that for every particle solution (`MovParticleSetup`)
and `t ≥ 0`: `H(f_t|Q_t) ≤ C (H(f_0|Q_0) + Nδ_N)`.  The hypothesis `GibbsEntropyContraction` of the frozen statement is not needed
(the finiteness of the Gibbs entropy of the initial law is derived from `H(f_0|Q_0) < ∞`, `s66_gibbs_finite`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

/-- The canonical Gibbs law of the quadratic confinement is `Q_{N,β}(ρ₀)`. -/
theorem s66_canonical_eq (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : Whole.IsThermalEquilibrium d s q β ρ₀) (N : ℕ) :
    Whole.canonicalGibbs (rieszKernel d s) (confinement q) N β =
      Whole.modulatedGibbs (rieszKernel d s) N β (wd ρ₀) := by
  have hρ := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd hq hβ hρ₀
  have hth : thermalMeasure d s q β = wd ρ₀ := by
    unfold thermalMeasure; rw [hρ]
  rw [← hth]
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    exact HRS.MS.Can2.logThermal_canonical_proof hd q β hq hβ N
  · exact (HRS.MS.Can2.euc_thermal_canonical_proof hd hpos hsd q β hq hβ).1 N

end HRS.MS.MovEnt

end
