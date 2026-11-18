import HRS.MS.Fp81S21InitialFutureLaw
import HRS.MS.Fp81S21InitialFutureLaw4
import HRS.MS.Fp81S21InitialFutureLaw5

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- The synthesized initial Gaussian and the restricted zero-cutoff future,
independently sampled, sum to the law of every Gaussian realization's window. -/
theorem fp81s21_initial_future_window_law (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∀ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H),
          ((∀ H v, IsProbabilityMeasure (future H v)) ∧
            ∀ H : ℝ, 0 < H → ∀ v ∈ Set.Icc (0 : ℝ) H,
              IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d) H v (future H v)) →
        ∀ a : ℝ, ∀ ha : 0 ≤ a,
        ∀ (G : Measure SeqL2) [IsProbabilityMeasure G],
          IsCenteredGaussianSeq G (fun j k =>
            HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
              (r26t3_qwin R a j) (r26t3_qwin R a k)) →
        ∀ G0 : GaussianRealization R,
          Measure.map (fun yy : Window p × Window p => yy.1 + yy.2)
            ((Measure.map (fp81s21_initGauss_synthesis p) G).prod
              (windowFuture future a ha 0)) = law G0.P (r26t3_Zpath G0 a) := by
  obtain ⟨δ26, hδ26, hδhalf, hinitial⟩ := fp81s21_initial_future_initial_fdd p
  refine ⟨δ26, hδ26, hδhalf, ?_⟩
  intro δ hδ hδle R _ future hf a ha G _ hG G0
  letI : IsProbabilityMeasure (future (a + p.T) 0) := hf.1 (a + p.T) 0
  letI : IsProbabilityMeasure (Measure.map (fp81s21_initGauss_synthesis p) G) :=
    (Measure.isProbabilityMeasure_map_iff
      (fp81s21_initGauss_synthesis p).continuous.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (windowFuture future a ha 0) := by
    unfold windowFuture
    exact (Measure.isProbabilityMeasure_map_iff
      (physicalWindowRestriction (d := p.d) (m := wholeSpaceIndex p.d)
        (T := p.T) (H := a + p.T) ha le_rfl).continuous.aemeasurable).2 inferInstance
  have hH : 0 < a + p.T := by linarith [p.hT]
  have hcut : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (a + p.T) := ⟨le_rfl, hH.le⟩
  exact fp81s21_initial_future_window_law_of_finite_gaussian p R G0 a ha
    (Measure.map (fp81s21_initGauss_synthesis p) G) (windowFuture future a ha 0)
    (hinitial δ hδ hδle R a ha G hG)
    (fp81s21_initial_future_noise_fdd p R future a ha (hf.2 (a + p.T) hH 0 hcut))

#print axioms fp81s21_initial_future_window_law

end HRS.Fp81.S21

end
