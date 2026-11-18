import HRS.MS.WsPrepAux15
import HRS.MS.S21F_D01

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- A Gaussian realization's window law is the independent sum of any two
probability laws having its transported initial and noise finite-dimensional
Gaussian laws. -/
theorem fp81s21_initial_future_window_law_of_finite_gaussian
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (G0 : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (γ0 Γ : Measure (Window p)) [IsProbabilityMeasure γ0] [IsProbabilityMeasure Γ]
    (hγ : ∀ (n : ℕ) (ts : Fin n → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) p.T)
        (αs : Fin n → MultiIndex p.d),
      (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (propagatorW (r26t3_coeff R) 0 (a + ts i) (oscTestFun (wholeSpaceIndex p.d) (αs i)))
        (propagatorW (r26t3_coeff R) 0 (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs j)))).PosSemidef ∧
      γ0.map (fun w : Window p => (WithLp.toLp 2 fun i => OscDual.coord
        (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j =>
          HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (propagatorW (r26t3_coeff R) 0 (a + ts i) (oscTestFun (wholeSpaceIndex p.d) (αs i)))
            (propagatorW (r26t3_coeff R) 0 (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs j)))))
    (hΓ : ∀ (n : ℕ) (ts : Fin n → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) p.T)
        (αs : Fin n → MultiIndex p.d),
      (Matrix.of fun i j => noiseCovW (r26t3_coeff R) p.β⁻¹ (a + ts i) (a + ts j)
        (oscTestFun (wholeSpaceIndex p.d) (αs i)) (oscTestFun (wholeSpaceIndex p.d) (αs j))).PosSemidef ∧
      Γ.map (fun w : Window p => (WithLp.toLp 2 fun i => OscDual.coord
        (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j => noiseCovW (r26t3_coeff R) p.β⁻¹
          (a + ts i) (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs i))
          (oscTestFun (wholeSpaceIndex p.d) (αs j)))) :
    Measure.map (fun z : Window p × Window p => z.1 + z.2) (γ0.prod Γ) =
      law G0.P (r26t3_Zpath G0 a) := by
  exact (s21p_Zwin_law p.hT.le ha G0.P (G0.evolution (a + p.T)) γ0 Γ hγ hΓ).symm

#print axioms fp81s21_initial_future_window_law_of_finite_gaussian

end HRS.Fp81.S21

end
