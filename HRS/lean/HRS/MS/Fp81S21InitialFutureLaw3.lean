import HRS.MS.Fp81S21InitialFutureLaw2
import HRS.MS.WsInitGAux10

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21

/-- The synthesized centered sequence Gaussian has the stated finite-window
Gaussian law whenever its coordinate products have the stated covariances. -/
theorem fp81s21_initial_future_synthesis_fdd
    (p : Parameters) (G : Measure SeqL2) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussian G) (n : ℕ) (ts : Fin n → ℝ)
    (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) p.T) (αs : Fin n → MultiIndex p.d)
    (C : Fin n → Fin n → ℝ)
    (hcov : ∀ i j,
      (∫ y, fp81s21_windowCoordCLM p ⟨ts i, hts i⟩ (αs i) y *
        fp81s21_windowCoordCLM p ⟨ts j, hts j⟩ (αs j) y
        ∂(Measure.map (fp81s21_initGauss_synthesis p) G)) = C i j) :
    (Matrix.of C).PosSemidef ∧
    (Measure.map (fp81s21_initGauss_synthesis p) G).map
      (fun w : Window p => (WithLp.toLp 2 fun i => OscDual.coord
        (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of C) := by
  letI : IsGaussian G := hG.1
  let σ := r26t3_feature_enum p.d
  let w : Fin n → SeqL2 := fun i => s21gVec σ p.hT (ts i) (αs i)
  have hmean : ∫ z, id z ∂G = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hG
  have hev (i : Fin n) (z : SeqL2) :
      fp81s21_windowCoordCLM p ⟨ts i, hts i⟩ (αs i)
        (fp81s21_initGauss_synthesis p z) = inner ℝ (w i) z := by
    dsimp [w, σ, fp81s21_initGauss_synthesis]
    rw [fp81s21_windowCoordCLM_apply]
    exact s21gPhi_coord_inner (r26t3_feature_enum p.d) p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ) z ⟨ts i, hts i⟩ (αs i)
  have hmat : (Matrix.of fun i j => covarianceBilin G (w i) (w j)) = Matrix.of C := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, covarianceBilin_apply IsGaussian.memLp_two_id, hmean]
    simp only [id, sub_zero]
    simp_rw [← hev i, ← hev j]
    have hm : AEStronglyMeasurable (fun y : Window p =>
        fp81s21_windowCoordCLM p ⟨ts i, hts i⟩ (αs i) y *
        fp81s21_windowCoordCLM p ⟨ts j, hts j⟩ (αs j) y)
        (Measure.map (fp81s21_initGauss_synthesis p) G) :=
      ((fp81s21_windowCoordCLM p ⟨ts i, hts i⟩ (αs i)).continuous.mul
        (fp81s21_windowCoordCLM p ⟨ts j, hts j⟩ (αs j)).continuous).aestronglyMeasurable
    have heq := integral_map (fp81s21_initGauss_synthesis p).continuous.aemeasurable hm
    exact heq.symm.trans (hcov i j)
  obtain ⟨hpsd, hlaw⟩ := s21g_fdd_gaussian G hmean w
  rw [hmat] at hpsd hlaw
  refine ⟨hpsd, ?_⟩
  have hFm : Measurable (fun y : Window p => (WithLp.toLp 2 fun i =>
      OscDual.coord (OscPath.at' y ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) := by
    refine ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)).measurable
    exact (fp81s21_windowCoordCLM p ⟨ts i, hts i⟩ (αs i)).continuous
  rw [Measure.map_map hFm (fp81s21_initGauss_synthesis p).continuous.measurable]
  convert hlaw using 2
  funext z
  ext i
  simp only [Function.comp_apply, s21gAw_apply]
  exact hev i z

#print axioms fp81s21_initial_future_synthesis_fdd

end HRS.Fp81.S21

end
