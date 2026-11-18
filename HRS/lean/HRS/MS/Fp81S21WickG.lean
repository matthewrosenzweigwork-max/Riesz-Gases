import HRS.MS.Fp81S21GaussLin2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The finite-dimensional law of oscillator observations at one nonnegative
time, with the covariance matrix read directly from the supplied evolution.
The horizon is chosen as `u + 1`, so the law is available for every `u ≥ 0`.
-/
theorem fp81s21_wickG_oscillator_joint_law
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) {u : ℝ} (hu : 0 ≤ u)
    {n : ℕ} (φ : Fin n → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) :
    G.P.map (fun ω =>
      (WithLp.toLp 2 (fun i => OscDual.eval (G.Z u ω) (φ i) : Fin n → ℝ) :
        EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j =>
        linearGaussianCov (r26t3_coeff R) p.β⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
            (r26t3_mu R 0) p.γ)
          u u (φ i) (φ j)) := by
  have htime : ∀ i : Fin n, u ∈ Set.Icc (0 : ℝ) (u + 1) := by
    intro i
    exact ⟨hu, by linarith⟩
  have h := (G.evolution (u + 1)).gaussian n (fun _ => u) φ htime hφ
  simpa [HRS.Whole.linearGaussianCov] using h

#print axioms fp81s21_wickG_oscillator_joint_law

end HRS.Fp81.S21

end
