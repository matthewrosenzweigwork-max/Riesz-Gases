import HRS.MS.GenPathAux48

/-!
# S5.6 packet P7g: the coordinate arrays of the prescribed initial path and of the Gaussian part of `Y`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

/-- The coordinate array of the process `Y` at the times `s n`. -/
def s56Psi0 {m T : ℝ} {Ω : Type*} (s : ℕ → Set.Icc (0 : ℝ) T) (Y : ℝ → Ω → OscDual d m) (ζ : Ω) :
    ℕ × MultiIndex d → ℝ := fun i => OscDual.coord (Y (s i.1) ζ) i.2

/-- The coordinate array `A η₀(U^{0,s n} φ_α)` of the prescribed initial path. -/
def s56Psic {b : WholeBounds d} (S : WholeSetup b) (N : ℕ) {Ω : Type*} (s : ℕ → Set.Icc (0 : ℝ) b.T)
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (ζ : Ω) : ℕ × MultiIndex d → ℝ :=
  fun i => S.A N * η₀ ζ (propagatorW (S.coeff N) 0 (s i.1) (oscTestFun b.m i.2))

theorem s56_Psi0_meas {m T : ℝ} {Ω : Type*} [MeasurableSpace Ω] (s : ℕ → Set.Icc (0 : ℝ) T)
    (Y : ℝ → Ω → OscDual d m) (hY : ∀ t, Measurable (Y t)) : Measurable (s56Psi0 s Y) :=
  measurable_pi_iff.2 fun i => (s56_continuous_coord m i.2).measurable.comp (hY _)

/-- Finite-dimensional structure of the Gaussian part of `Y`: the vector `V_D = (Ψ₀ - Ψc)_f` is independent of `η₀`
and has the Gaussian law with the noise covariance. -/
theorem s56_VD_law (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d b.m)
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (s : ℕ → Set.Icc (0 : ℝ) b.T) {p : ℕ} (f : Fin p → ℕ × MultiIndex d) :
    IndepFun (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p))) (fun ζ f => S.A N * η₀ ζ f) P ∧
    P.map (fun ζ => (WithLp.toLp 2 fun a => s56Psi0 s Y ζ (f a) - s56Psic S N s η₀ ζ (f a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N)
        (s (f a).1) (s (f c).1) (oscTestFun b.m (f a).2) (oscTestFun b.m (f c).2)) := by
  have h := hY.gaussian_part p (fun a => (s (f a).1 : ℝ)) (fun a => oscTestFun b.m (f a).2)
    (fun a => (s (f a).1).2) (fun a => s56_isOscTest b.m (f a).2)
  simp only [OscDual.eval_oscTestFun] at h
  exact h

end HRS.MS.GenPath
