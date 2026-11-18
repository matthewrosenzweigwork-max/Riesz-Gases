import HRS.MS.Fp81S21CoeffCenter3
import HRS.MS.Fp81S21WickMomRep8

/-! Centering exports for the particle actual-law-centered quadratic field
and the Gaussian Wick quadratic field. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- This particle export centers only the quadratic field already centered
under the realization law. Its raw pre-centering field is not asserted to
have zero mean. -/
abbrev fp81s21_centerCor_particle_quad :=
  fp81s21_particleQuadCoeff_firstMoment_centered

private theorem fp81s21_centerCor_chartAction_test_coordinate
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction E z (E.test j) = z j := by
  have hcoord : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, hcoord]
  simpa [lp.inner_single_right]

/-- The strong and embedded coefficients representing the Gaussian Wick
quadratic field are Bochner integrable and have zero means. The strong
centering is obtained by applying fp81s21_wickB312_centered to the same
supplied half-Wick operator selected by the moment representation. -/
theorem fp81s21_centerCor_gaussian_wick (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ Kstar B : ℝ, 0 ≤ Kstar ∧ 0 ≤ B ∧
          ∀ G : GaussianRealization R,
            ∃ qsB qB : ℝ → G.Ω → r26t6_Coeff,
              qB = (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsB u ω)) ∧
              fp81s21_MomentRep Es G.P
                (fp81s21_wickChartField Es qsB) qsB
                (Kstar ^ 4 * B / 2) ∧
              fp81s21_MomentRep E G.P
                (fp81s21_wickChartField Es qsB) qB
                (Kstar ^ 4 * B / 2) ∧
              ∀ u : ℝ, 0 ≤ u →
                (AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                    ((p.d : ℝ) + 4)
                    (fp81s21_wickChartField Es qsB u ω)) G.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_wickChartField Es qsB u ω) ∂G.P) ≤
                    ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) ∧
                Integrable (qsB u) G.P ∧
                (∫ ω, qsB u ω ∂G.P) = 0 ∧
                (AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                    ((p.d : ℝ) + 2)
                    (fp81s21_wickChartField Es qsB u ω)) G.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                    (fp81s21_wickChartField Es qsB u ω) ∂G.P) ≤
                    ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) ∧
                Integrable (qB u) G.P ∧
                (∫ ω, qB u ω ∂G.P) = 0 := by
  obtain ⟨δ0, hδ0, hδhalf, hWick⟩ :=
    fp81s21_wick_momentRep_physical p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨Kstar, B, hK, hB, hForG⟩ :=
    hWick δ hδ hδle R Es E
  refine ⟨Kstar, B, hK, hB, ?_⟩
  intro G
  obtain ⟨T, W, qsB, hW, hT, hStrong, hWeak, hAgree, _hFirst⟩ :=
    hForG G
  let qB : ℝ → G.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsB u ω)
  have hMeanStrong : ∀ u, 0 ≤ u → (∫ ω, qsB u ω ∂G.P) = 0 := by
    intro u hu
    letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
      HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
    obtain ⟨hL, hJoint, hWop⟩ := hW u hu
    let L := T u
    have hCoordMean : ∀ j : ℕ, ∫ ω, qsB u ω j ∂G.P = 0 := by
      intro j
      let f : Euc p.d → ℝ := Es.test j
      obtain ⟨hker, hSection⟩ := hAgree u hu f (Es.test_smooth j)
      have hCoordAE : (fun ω => qsB u ω j) =ᵐ[G.P]
          (fun ω => (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ) ω) := by
        filter_upwards [hSection] with ω hWω
        calc
          qsB u ω j = fp81s21_chartAction Es (qsB u ω) (Es.test j) :=
            (fp81s21_centerCor_chartAction_test_coordinate Es (qsB u ω) j).symm
          _ = fp81s21_wickChartField Es qsB u ω f := by rfl
          _ = (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
                commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ) ω :=
            hWω
      have hMeanW :
          (∫ ω, (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ) ω
            ∂G.P) = 0 := by
        calc
          _ = ∫ ω, (fp81s21_wickFam_operator R G L Kstar hL hJoint
              (hker.toLp (fun xy : Euc p.d × Euc p.d =>
                commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ) ω
              ∂G.P := by rw [hWop]
          _ = 0 := by
            simpa [fp81s21_wickFam_operator] using
              (fp81s21_wickB312_centered L Kstar hL hJoint
                (hker.toLp (fun xy : Euc p.d × Euc p.d =>
                  commutatorKernel p.d p.s (gradient f) xy.1 xy.2)))
      exact (integral_congr_ae hCoordAE).trans hMeanW
    have hqInt : Integrable (qsB u) G.P :=
      (hStrong.2 u hu).1.integrable one_le_two
    apply lp.ext (funext fun j => ?_)
    have hComm :=
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).integral_comp_comm hqInt
    change (∫ ω, qsB u ω j ∂G.P) = (∫ ω, qsB u ω ∂G.P) j at hComm
    rw [hCoordMean j] at hComm
    exact hComm.symm
  let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    fp81s21_gaussian_chartEmbed p Es E
  refine ⟨qsB, qB, ?_, hStrong, ?_, ?_⟩
  · rfl
  · simpa [qB] using hWeak
  · intro u hu
    have hFirstStrong :=
      fp81s21_MomentRep_firstMoment Es G.P
        (fp81s21_wickChartField Es qsB) qsB
        (Kstar ^ 4 * B / 2) hStrong u hu
    have hFirstWeak :=
      fp81s21_MomentRep_firstMoment E G.P
        (fp81s21_wickChartField Es qsB) qB
        (Kstar ^ 4 * B / 2) hWeak u hu
    have hStrongInt : Integrable (qsB u) G.P :=
      (hStrong.2 u hu).1.integrable one_le_two
    have hWeakInt : Integrable (qB u) G.P :=
      (hWeak.2 u hu).1.integrable one_le_two
    have hMeanWeak : (∫ ω, qB u ω ∂G.P) = 0 := by
      rw [K.integral_comp_comm hStrongInt, hMeanStrong u hu]
      simp
    exact ⟨hFirstStrong, hStrongInt, hMeanStrong u hu,
      hFirstWeak, hWeakInt, by simpa [qB, K] using hMeanWeak⟩

#print axioms HRS.Fp81.S21.fp81s21_centerCor_particle_quad
#print axioms HRS.Fp81.S21.fp81s21_centerCor_gaussian_wick

end HRS.Fp81.S21
end
