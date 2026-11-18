import HRS.MS.Fp81S21GaussianW0

/-! Packet 37, unit 7: partial result, the initial cubic integrability clause.

This file does not assert `fp81s21_gaussian_wick_time`. The four spatial/time
clauses and absolute probability-time domination remain open. In particular,
endpoint mixed moments do not provide domination of the time densities.
The radius below is inherited from GaussianW0 and precedes all trajectories
and observation data. No physical realization or density family is needed
for this first clause of `CubicFormulaIntegrable`.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The first clause of the requested moving cubic formula integrability,
with the dynamical coefficient and initial measure written as in its definition. -/
theorem fp81s21_gaussian_wick_time_initial (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ a : ℝ, 0 ≤ a → ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T)
        (φ : Fin 3 → Euc p.d → ℝ),
      (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
      let g := fun i => HRS.Whole.responseInverse (rieszKernel p.d p.s)
        (HRS.Whole.withDensityReal (R.ρ 0)) p.γ
        (propagatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ)
          0 (a + τ i) (φ i))
      Integrable (fun x => g 0 x * g 1 x * g 2 x)
        (HRS.Whole.withDensityReal (R.ρ 0)) := by
  obtain ⟨δ₀, hδ₀, hhalf, hW0⟩ := fp81s21_gaussian_W0 p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R a ha τ φ hφ
  exact (hW0 δ hδ hδle R a ha τ φ hφ).2

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_time_initial
