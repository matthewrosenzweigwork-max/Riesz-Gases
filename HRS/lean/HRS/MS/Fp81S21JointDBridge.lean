import HRS.MS.Fp81S21JointD6
import HRS.MS.Fp81S21JointN2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The two definitions of the raw rank polynomial coincide. -/
theorem fp81s21_polyAtD_eq_polyAt {d : ℕ} (D : fp81s21_RankKernel d)
    (η : OscDual d (wholeSpaceIndex d : ℝ)) :
    fp81s21_polyAtD D η = fp81s21_polyAt D η := by
  simp [fp81s21_polyAtD, fp81s21_constantEtaPath, fp81s21_quadPoly,
    OscPath.at', fp81s21_polyAt]

/-- Both constructions use the same empirical fluctuation. -/
theorem fp81s21_rawEtaAt_eq_jointN_rawEtaAt {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) {N : ℕ} (A : Particle R N) (u : ℝ) (ω : A.Ω) :
    fp81s21_rawEtaAt R A u ω = fp81s21_jointN_rawEtaAt R A u ω := rfl

/-- The particle raw time-class contract is exactly the representative form
consumed by the diagonal estimate. -/
theorem fp81s21_particleRawPolynomialTime31_iff
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (A : Particle R N) (a H : ℝ)
    (Uraw : A.Ω → fp81s21_jointP_U H) :
    fp81s21_ParticleRawPolynomialTime31 p R m Λ θ D k N A a H Uraw ↔
    ∃ Mraw : ℝ, ∃ qraw : ℝ → A.Ω → r26t6_Coeff,
      Measurable (Function.uncurry qraw) ∧
      (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
        qraw u ω = ∑ j : Fin m,
          fp81s21_polyAtD (D (θ j) k) (fp81s21_rawEtaAt R A u ω) •
            fp81s21_coeffBasis j) ∧
      fp81s21_TimeL2Rep A.P qraw Mraw a H Uraw := by
  simp only [fp81s21_ParticleRawPolynomialTime31, fp81s21_polyAtD_eq_polyAt,
    fp81s21_rawEtaAt_eq_jointN_rawEtaAt]

#print axioms fp81s21_polyAtD_eq_polyAt
#print axioms fp81s21_rawEtaAt_eq_jointN_rawEtaAt
#print axioms fp81s21_particleRawPolynomialTime31_iff
end HRS.Fp81.S21
end
