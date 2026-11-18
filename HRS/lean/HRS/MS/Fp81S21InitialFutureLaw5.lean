import HRS.MS.Fp81S21InitialWindow
import HRS.MS.R2InterpAux5

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.ProClosureS111

/-- Restricting a zero-cutoff future gives the required noise Gaussian
finite-dimensional laws on the shifted window. -/
theorem fp81s21_initial_future_noise_fdd
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (a : ℝ) (ha : 0 ≤ a)
    (hf : IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d) (a + p.T) 0
      (future (a + p.T) 0))
    (n : ℕ) (ts : Fin n → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) p.T)
    (αs : Fin n → MultiIndex p.d) :
    (Matrix.of fun i j => noiseCovW (r26t3_coeff R) p.β⁻¹ (a + ts i) (a + ts j)
      (oscTestFun (wholeSpaceIndex p.d) (αs i)) (oscTestFun (wholeSpaceIndex p.d) (αs j))).PosSemidef ∧
    (windowFuture future a ha 0).map
      (fun w : Window p => (WithLp.toLp 2 fun i => OscDual.coord
        (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j => noiseCovW (r26t3_coeff R) p.β⁻¹
        (a + ts i) (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs i))
        (oscTestFun (wholeSpaceIndex p.d) (αs j))) := by
  let τ : Fin n → Set.Icc (0 : ℝ) (a + p.T) := fun i =>
    physicalWindowTime ha le_rfl ⟨ts i, hts i⟩
  have hc : s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d) τ αs 0 =
      Matrix.of (fun i j => noiseCovW (r26t3_coeff R) p.β⁻¹ (a + ts i) (a + ts j)
        (oscTestFun (wholeSpaceIndex p.d) (αs i)) (oscTestFun (wholeSpaceIndex p.d) (αs j))) := by
    ext i j
    simp [s102_obsCov, noiseCovW, τ, physicalWindowTime, r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn]
  have hl := s102_obs_law (r26t3_coeff R) hf τ αs
  rw [hc] at hl
  refine ⟨hl.1, ?_⟩
  have hFm : Measurable (fun w : Window p => (WithLp.toLp 2 fun i =>
      OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) := by
    have he : (fun w : Window p => (WithLp.toLp 2 fun i =>
        OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
        s102_obs (fun i => ⟨ts i, hts i⟩) αs := by
      funext w
      ext i
      rfl
    rw [he]
    exact (s102_obs (fun i => ⟨ts i, hts i⟩) αs).continuous.measurable
  unfold windowFuture
  rw [Measure.map_map hFm (physicalWindowRestriction (d := p.d) (m := wholeSpaceIndex p.d)
    (T := p.T) (H := a + p.T) ha le_rfl).continuous.measurable]
  convert hl.2 using 2
  funext w
  ext i
  rfl

#print axioms fp81s21_initial_future_noise_fdd

end HRS.Fp81.S21

end
