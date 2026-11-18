import HRS.MS.Fp81S21GaussLaw2
import HRS.MS.GenPathAux36
import HRS.Main.GFB4Aux13

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.GenPath

/-- The Gaussian part of the R26-T3 error is determined by the realization law,
including the expectation of the third derivative pairing. -/
theorem fp81s21_r26t3_error_realization_invariant
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (G0 : GaussianRealization R)
    (κ : ℝ → projTensor (Window p) 3)
    {N : ℕ} (A : Particle R N) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a)
    (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5) :
    r26t3_error κ A G a Φ = r26t3_error κ A G0 a Φ := by
  let m : ℝ := wholeSpaceIndex p.d
  let Y : ℝ → G.Ω → OscDual p.d (wholeSpaceIndex p.d) :=
    fun t ζ => G.Z (a + t) ζ
  let Y0 : ℝ → G0.Ω → OscDual p.d (wholeSpaceIndex p.d) :=
    fun t ζ => G0.Z (a + t) ζ
  have hcontG : ∀ᵐ ζ ∂G.P,
      ContinuousOn (fun t : ℝ => G.Z (a + t) ζ) (Set.Icc (0 : ℝ) p.T) := by
    have hH : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
    filter_upwards [(G.evolution (a + p.T)).cont] with ζ hζ
    exact hζ.comp (continuousOn_const.add continuousOn_id) fun t ht =>
      ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
  have hcontG0 : ∀ᵐ ζ ∂G0.P,
      ContinuousOn (fun t : ℝ => G0.Z (a + t) ζ) (Set.Icc (0 : ℝ) p.T) := by
    have hH : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
    filter_upwards [(G0.evolution (a + p.T)).cont] with ζ hζ
    exact hζ.comp (continuousOn_const.add continuousOn_id) fun t ht =>
      ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
  have hIdMeas : Measurable
      (fun z : HRS.Uniform.PathSp p.T (OscDual p.d m) => (z : Window p)) := by
    exact continuous_id.measurable
  have hpathMeasG : AEMeasurable (r26t3_Zpath G a) G.P := by
    have hUniform := HRS.GF.gfb4_aemeasurable_windowPath G.P p.hT.le Y
      (fun t _ => (G.evolution (a + p.T)).meas (a + t)) hcontG
    have hUniformOsc : AEMeasurable
        (fun ζ => (HRS.Uniform.windowPath 0 p.T Y ζ : Window p)) G.P :=
      hIdMeas.comp_aemeasurable hUniform
    have hshift : r26t3_Zpath G a =
        (fun ζ => (HRS.Uniform.windowPath 0 p.T Y ζ : Window p)) := by
      simpa only [processWindow] using
        (show r26t3_Zpath G a = processWindow m p.T 0 Y from by
          funext ζ
          simpa [r26t3_Zpath, Y] using
            (HRS.Whole.S79.s79p_processWindow_shift p.T a G.Z ζ)).trans
          (s56_wpo_eq_windowPath Y)
    rw [hshift]
    exact hUniformOsc
  have hpathMeasG0 : AEMeasurable (r26t3_Zpath G0 a) G0.P := by
    have hUniform := HRS.GF.gfb4_aemeasurable_windowPath G0.P p.hT.le Y0
      (fun t _ => (G0.evolution (a + p.T)).meas (a + t)) hcontG0
    have hUniformOsc : AEMeasurable
        (fun ζ => (HRS.Uniform.windowPath 0 p.T Y0 ζ : Window p)) G0.P :=
      hIdMeas.comp_aemeasurable hUniform
    have hshift : r26t3_Zpath G0 a =
        (fun ζ => (HRS.Uniform.windowPath 0 p.T Y0 ζ : Window p)) := by
      simpa only [processWindow] using
        (show r26t3_Zpath G0 a = processWindow m p.T 0 Y0 from by
          funext ζ
          simpa [r26t3_Zpath, Y0] using
            (HRS.Whole.S79.s79p_processWindow_shift p.T a G0.Z ζ)).trans
          (s56_wpo_eq_windowPath Y0)
    rw [hshift]
    exact hUniformOsc
  have hLaw := fp81s21_gaussian_window_law_eq p R G0 G a ha
  have hΦcont : Continuous Φ := hΦ.1.continuous
  have hD3cont : Continuous (iteratedFDeriv ℝ 3 Φ) :=
    hΦ.1.continuous_iteratedFDeriv (by norm_num)
  have hCubicCont : Continuous (fun z : Window p =>
      (κ a : TensorDual (Window p) 3) (iteratedFDeriv ℝ 3 Φ z)) :=
    (κ a : TensorDual (Window p) 3).continuous.comp hD3cont
  have htestG :
      (∫ ζ, Φ (r26t3_Zpath G a ζ) ∂G.P) =
        ∫ z, Φ z ∂law G.P (r26t3_Zpath G a) := by
    rw [HRS.law]
    exact (integral_map hpathMeasG hΦcont.aestronglyMeasurable).symm
  have htestG0 :
      (∫ ζ, Φ (r26t3_Zpath G0 a ζ) ∂G0.P) =
        ∫ z, Φ z ∂law G0.P (r26t3_Zpath G0 a) := by
    rw [HRS.law]
    exact (integral_map hpathMeasG0 hΦcont.aestronglyMeasurable).symm
  have hthirdG :
      (∫ ζ, (κ a : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ζ)) ∂G.P) =
        ∫ z, (κ a : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ z) ∂law G.P (r26t3_Zpath G a) := by
    rw [HRS.law]
    exact (integral_map hpathMeasG hCubicCont.aestronglyMeasurable).symm
  have hthirdG0 :
      (∫ ζ, (κ a : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G0 a ζ)) ∂G0.P) =
        ∫ z, (κ a : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ z) ∂law G0.P (r26t3_Zpath G0 a) := by
    rw [HRS.law]
    exact (integral_map hpathMeasG0 hCubicCont.aestronglyMeasurable).symm
  have htest :
      (∫ ζ, Φ (r26t3_Zpath G a ζ) ∂G.P) =
        ∫ ζ, Φ (r26t3_Zpath G0 a ζ) ∂G0.P := by
    rw [htestG, htestG0, hLaw]
  have hthird :
      (∫ ζ, (κ a : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ζ)) ∂G.P) =
        ∫ ζ, (κ a : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G0 a ζ)) ∂G0.P := by
    rw [hthirdG, hthirdG0, hLaw]
  unfold r26t3_error
  rw [htest, hthird]

#print axioms fp81s21_r26t3_error_realization_invariant

end HRS.Fp81.S21

end
