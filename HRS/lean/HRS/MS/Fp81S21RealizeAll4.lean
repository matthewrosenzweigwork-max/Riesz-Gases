import HRS.MS.Fp81S21RealizeAll3
import HRS.MS.Fp81S21RawEval2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- Transfer the retained raw finite-dimensional laws through the patched
fixed-time a.e. equalities and fill every field of `IsLinearGaussianEvolutionW`.
The covariance identity is by unfolding the compiled `linearGaussianCov`. -/
theorem fp81s21_realize_evolution_all_horizons
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Z Z0 : ℝ → Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ))
    (hZmeas : ∀ t, Measurable (Z t))
    (hZcont : ∀ ω, Continuous (fun t => Z t ω))
    (hmod : ∀ t, 0 ≤ t → Z t =ᵐ[P] Z0 t)
    (hRawLaw : ∀ (n : ℕ) (τ : Fin n → ℝ)
      (φ : Fin n → Euc p.d → ℝ),
      (∀ i, 0 ≤ τ i) →
      (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
      HRS.law P (fun ω => (WithLp.toLp 2 fun i =>
        OscDual.eval (Z0 (τ i) ω) (φ i) :
          EuclideanSpace ℝ (Fin n))) =
        ProbabilityTheory.multivariateGaussian 0
          (fp81s21_rawJointCovariance p R τ φ)) :
    ∀ H : ℝ,
      IsLinearGaussianEvolutionW P (r26t3_coeff R)
        (wholeSpaceIndex p.d) p.β⁻¹ H
        (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ) Z := by
  intro H
  refine ⟨?_, hZmeas, ?_⟩
  · by_cases hH : 0 ≤ H
    · filter_upwards [] with ω
      exact (hZcont ω).continuousOn
    · rw [Set.Icc_eq_empty (show ¬ (0 : ℝ) ≤ H by linarith)]
      exact Filter.Eventually.of_forall fun _ => continuousOn_empty _
  · intro n τ φ hτ hφ
    let G : Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
      WithLp.toLp 2 fun i => OscDual.eval (Z (τ i) ω) (φ i)
    let G0 : Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
      WithLp.toLp 2 fun i => OscDual.eval (Z0 (τ i) ω) (φ i)
    have hvec : G =ᵐ[P] G0 := by
      have hall : ∀ᵐ ω ∂P, ∀ i, G ω i = G0 ω i := by
        refine ae_all_iff.2 fun i => ?_
        have hi := (hmod (τ i) (hτ i).1).mono fun ω hω =>
          congrArg (fun z : OscDual p.d (wholeSpaceIndex p.d : ℝ) =>
            OscDual.eval z (φ i)) hω
        filter_upwards [hi] with ω hω
        simpa [G, G0] using hω
      filter_upwards [hall] with ω hω
      ext i
      exact hω i
    have hcov : fp81s21_rawJointCovariance p R τ φ =
        Matrix.of fun a b =>
          HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
              (propagatorW (r26t3_coeff R) 0 (τ a) (φ a))
              (propagatorW (r26t3_coeff R) 0 (τ b) (φ b)) +
            noiseCovW (r26t3_coeff R) p.β⁻¹
              (τ a) (τ b) (φ a) (φ b) := by
      ext a b
      simp [fp81s21_rawJointCovariance, HRS.Whole.linearGaussianCov]
    calc
      HRS.law P G = HRS.law P G0 := Measure.map_congr hvec
      _ = ProbabilityTheory.multivariateGaussian 0
            (fp81s21_rawJointCovariance p R τ φ) :=
          hRawLaw n τ φ (fun i => (hτ i).1) hφ
      _ = ProbabilityTheory.multivariateGaussian 0
            (Matrix.of fun a b =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                  (propagatorW (r26t3_coeff R) 0 (τ a) (φ a))
                  (propagatorW (r26t3_coeff R) 0 (τ b) (φ b)) +
                noiseCovW (r26t3_coeff R) p.β⁻¹
                  (τ a) (τ b) (φ a) (φ b)) := by
          rw [hcov]

#print axioms fp81s21_realize_evolution_all_horizons

end HRS.Fp81.S21

end
