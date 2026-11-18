import HRS.MS.Fp81S21Uniform

/-!
# HRS S2.1(iii), higher particle marginal weights

The uniform density package records one fixed particle marginal moment.  The
actual-density marginal theorem upgrades that to any nonnegative polynomial
weight, with its constant selected after the trajectory and exponent but
before the particle count, realization, and time.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole
open HRS.MS.R26T3

/-- Every nonnegative polynomial weight has a uniform particle-marginal
moment bound along the trajectory.  The exponent-dependent constant is fixed
before the particle count, particle realization, and time. -/
theorem fp81s21_uniform_higher_marginal_weights (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ w : ℝ, 0 ≤ w →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ N : ℕ, 2 ≤ N → ∀ (A : Particle R N), ∀ u : ℝ, 0 ≤ u →
              Integrable (fun x : Euc p.d => jbracket x ^ w)
                (HRS.Whole.meanEmpirical (law A.P (A.X u.toNNReal))) ∧
              (∫ x : Euc p.d, jbracket x ^ w
                ∂(HRS.Whole.meanEmpirical (law A.P (A.X u.toNNReal)))) ≤ C := by
  obtain ⟨δ0, hδ0, hδ0half, hUniform⟩ := fp81s21_uniform_density_moments p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R w hw
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hgaussian, hround2, _, hparticle⟩ := hUniform δ hδ hδle R
  obtain ⟨Cbase, hC⟩ := HRS.MS.R2Interp.s102_marginal_moment_bound
    p.hd p.hs0 p.hs M L C₀ c₀ p.β pinf K hc₀ p.hβ hpinf
    (Pw := w) hw
  let C : ℝ := max Cbase 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro N hN A u hu
  have hparticle' := hparticle N hN A u hu
  have hactual := hparticle'.1
  have hρ := hround2 u hu
  have hG := (hgaussian u hu).2
  have hIntegrable := HRS.MS.R2Interp.s102_marginal_moment
    p.hd p.hs0 p.hs M L C₀ c₀ p.β pinf K hc₀ p.hβ hpinf
    (Pw := w) hw hρ hG hN hactual
  have hBound := (hC hρ hG hN hactual).trans (le_max_left Cbase (0 : ℝ))
  exact ⟨hIntegrable, hBound⟩

#print axioms fp81s21_uniform_higher_marginal_weights

end HRS.Fp81.S21

end
