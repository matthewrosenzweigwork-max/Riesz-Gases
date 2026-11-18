import HRS.MS.S21F_D01
import HRS.MS.GenPathAux42
import HRS.MS.GenPathAux47
import HRS.MS.ShiftFldAux8

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.GenPath

/-- Every realization of the same trajectory induces the same law on a Gaussian window. -/
theorem fp81s21_gaussian_window_law_eq
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (G0 : GaussianRealization R) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a) :
    law G.P (r26t3_Zpath G a) = law G0.P (r26t3_Zpath G0 a) := by
  let m : ℝ := wholeSpaceIndex p.d
  have hH : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
  haveI : Nonempty (Set.Icc (0 : ℝ) p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let s : ℕ → Set.Icc (0 : ℝ) p.T := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  let Y : ℝ → G.Ω → OscDual p.d (wholeSpaceIndex p.d) :=
    fun t ω => G.Z (a + t) ω
  let Y0 : ℝ → G0.Ω → OscDual p.d (wholeSpaceIndex p.d) :=
    fun t ω => G0.Z (a + t) ω
  let Ψ : G.Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    OscDual.coord (G.Z (a + (s i.1 : ℝ)) ω) i.2
  let Ψ0 : G0.Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    OscDual.coord (G0.Z (a + (s i.1 : ℝ)) ω) i.2
  have hΨm : Measurable Ψ := by
    apply measurable_pi_iff.2
    intro i
    exact (s56_continuous_coord m i.2).measurable.comp
      ((G.evolution (a + p.T)).meas (a + (s i.1 : ℝ)))
  have hΨ0m : Measurable Ψ0 := by
    apply measurable_pi_iff.2
    intro i
    exact (s56_continuous_coord m i.2).measurable.comp
      ((G0.evolution (a + p.T)).meas (a + (s i.1 : ℝ)))
  have hcoords : G.P.map Ψ = G0.P.map Ψ0 := by
    refine s56_seq_law_eq G.P G0.P Ψ Ψ0 hΨm.aemeasurable hΨ0m.aemeasurable ?_
    intro n f hf
    let τ : Fin n → ℝ := fun i => a + (s (f i).1 : ℝ)
    let φ : Fin n → Euc p.d → ℝ := fun i => oscTestFun m (f i).2
    have hτ : ∀ i, τ i ∈ Set.Icc (0 : ℝ) (a + p.T) := by
      intro i
      constructor
      · dsimp [τ]
        linarith [ha, (s (f i).1).2.1]
      · dsimp [τ]
        linarith [(s (f i).1).2.2]
    have hφ : ∀ i, IsOscTest m (φ i) := by
      intro i
      exact s56_isOscTest m (f i).2
    have hG := (G.evolution (a + p.T)).gaussian n τ φ hτ hφ
    have hG0 := (G0.evolution (a + p.T)).gaussian n τ φ hτ hφ
    have hvecG :
        (fun ζ => (WithLp.toLp 2 fun i => Ψ ζ (f i) : EuclideanSpace ℝ (Fin n))) =
          (fun ζ => (WithLp.toLp 2 fun i => OscDual.eval (G.Z (τ i) ζ) (φ i) :
            EuclideanSpace ℝ (Fin n))) := by
      funext ζ
      ext i
      exact (OscDual.eval_oscTestFun (G.Z (τ i) ζ) (f i).2).symm
    have hvecG0 :
        (fun ζ => (WithLp.toLp 2 fun i => Ψ0 ζ (f i) : EuclideanSpace ℝ (Fin n))) =
          (fun ζ => (WithLp.toLp 2 fun i => OscDual.eval (G0.Z (τ i) ζ) (φ i) :
            EuclideanSpace ℝ (Fin n))) := by
      funext ζ
      ext i
      exact (OscDual.eval_oscTestFun (G0.Z (τ i) ζ) (f i).2).symm
    have hG' :
        G.P.map (fun ζ => (WithLp.toLp 2 fun i => Ψ ζ (f i) : EuclideanSpace ℝ (Fin n))) =
          ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j =>
            HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (propagatorW (r26t3_coeff R) 0 (τ i) (φ i))
                (propagatorW (r26t3_coeff R) 0 (τ j) (φ j)) +
              noiseCovW (r26t3_coeff R) p.β⁻¹ (τ i) (τ j) (φ i) (φ j)) := by
      rw [hvecG]
      simpa only [HRS.law, HRS.Whole.linearGaussianCov] using hG
    have hG0' :
        G0.P.map (fun ζ => (WithLp.toLp 2 fun i => Ψ0 ζ (f i) : EuclideanSpace ℝ (Fin n))) =
          ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j =>
            HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (propagatorW (r26t3_coeff R) 0 (τ i) (φ i))
                (propagatorW (r26t3_coeff R) 0 (τ j) (φ j)) +
              noiseCovW (r26t3_coeff R) p.β⁻¹ (τ i) (τ j) (φ i) (φ j)) := by
      rw [hvecG0]
      simpa only [HRS.law, HRS.Whole.linearGaussianCov] using hG0
    exact hG'.trans hG0'.symm
  have hcontG : ∀ᵐ ω ∂G.P,
      ContinuousOn (fun t : ℝ => G.Z (a + t) ω) (Set.Icc (0 : ℝ) p.T) := by
    filter_upwards [(G.evolution (a + p.T)).cont] with ω hω
    exact hω.comp (continuousOn_const.add continuousOn_id) fun t ht =>
      ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
  have hcontG0 : ∀ᵐ ω ∂G0.P,
      ContinuousOn (fun t : ℝ => G0.Z (a + t) ω) (Set.Icc (0 : ℝ) p.T) := by
    filter_upwards [(G0.evolution (a + p.T)).cont] with ω hω
    exact hω.comp (continuousOn_const.add continuousOn_id) fun t ht =>
      ⟨by linarith [ha, ht.1], by linarith [ht.2]⟩
  have hpath := s56_path_law_eq (d := p.d) p.hT.le G.P G0.P Y Y0
    (fun t => (G.evolution (a + p.T)).meas (a + t))
    (fun t => (G0.evolution (a + p.T)).meas (a + t))
    hcontG hcontG0 s hs hcoords
  have hshiftG : r26t3_Zpath G a = processWindow m p.T 0 Y := by
    funext ω
    simpa [r26t3_Zpath, Y] using
      (HRS.Whole.S79.s79p_processWindow_shift p.T a G.Z ω)
  have hshiftG0 : r26t3_Zpath G0 a = processWindow m p.T 0 Y0 := by
    funext ω
    simpa [r26t3_Zpath, Y0] using
      (HRS.Whole.S79.s79p_processWindow_shift p.T a G0.Z ω)
  calc
    law G.P (r26t3_Zpath G a) = law G.P (fun ω => processWindow m p.T 0 Y ω) := by
      rw [hshiftG]
    _ = law G0.P (fun ω => processWindow m p.T 0 Y0 ω) := by
      simpa only [processWindow] using hpath
    _ = law G0.P (r26t3_Zpath G0 a) := by
      rw [← hshiftG0]

#print axioms fp81s21_gaussian_window_law_eq

end HRS.Fp81.S21

end
