import HRS.Main.HeadlineEquilibrium
import HRS.Equilibrium.StaticLimitsAux

/-!
# `HRS.Main.conditioned_ou`: statement-only packet specification (Chunk H)

The frozen theorem is a conjunction of three parts.  Parts (a) and (b) are stated separately below with exactly the
hypotheses and conclusions of the first and second conjunct.  Part (c) (convergence in law) is not specified here.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.CondOu

open HRS HRS.Main

variable {d : ℕ}

/-- **(a)** (size M, about 150 lines).  The Gibbs measure gives probability `1/2` to the event `{0 < ⟨ψ_k, η⟩}` for every nonzero lattice
point `k` and every `N ≥ 1`.  Route: generalise `HRS.StaticLimitsAux.prob_cos` (HRS/Equilibrium/StaticLimitsAux.lean:397, the case
`k = e_j`, `N = n+1`) using its helpers `prob_half` (:299), `gibbs_inv` (:359), `null_cos_sum` (:257): shifting one coordinate `x_i` with
`k_i ≠ 0` by `1/(2 k_i)` flips the sign of `cos(2π k·x)`, and the set `{Σ cos(2π k·x_i) = 0}` is null by Fubini in that coordinate. -/
theorem conditioned_ou_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) :
    ∀ N : ℕ, 1 ≤ N →
      (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β
        {X | 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) X}).toReal = 1 / 2 := by
  sorry

/-- **(b)** (size M, about 150 lines).  The third central moment of the half-normal mixture `ν_t` is positive for every `t ≥ 0`.
With `c = e^{-λt}√v > 0` and `G₀, G₁` independent standard Gaussians, `ν_t` is the law of `c|G₀| + √(v(1-e^{-2λt})) G₁`; the Gaussian part is
symmetric, so the third cumulant equals `c³ (E|G|³ - 3 E|G| E G² + 2 (E|G|)³) = c³ √(2/π) (4/π - 1) > 0` (TeX L7131).  Route: expand the cube of the
sum of independent variables (all odd moments of the centred Gaussian vanish), compute the half-line Gaussian integrals. -/
theorem conditioned_ou_third_cumulant (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) :
    ∀ t : ℝ, 0 ≤ t → 0 < thirdCentralMoment (halfNormalMixtureLaw d s β k t) := by
  sorry

end HRS.MH.CondOu
