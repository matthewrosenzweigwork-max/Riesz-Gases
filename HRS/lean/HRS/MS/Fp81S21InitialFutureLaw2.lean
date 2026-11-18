import HRS.MS.Fp81S21InitGaussIid
import HRS.MS.Fp81S21IidGaussUniq

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The common-radius initial covariance handoff holds for every centered
sequence Gaussian with the prescribed coordinate covariance. -/
theorem fp81s21_initial_future_supplied_covariance (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) → ∀ a : ℝ, 0 ≤ a →
          ∀ (G : Measure SeqL2) [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G (fun j k =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R a j) (r26t3_qwin R a k)) →
            ∀ u v : Set.Icc (0 : ℝ) p.T, ∀ α β : MultiIndex p.d,
              Integrable
                (fun y : Window p =>
                  fp81s21_windowCoordCLM p u α y * fp81s21_windowCoordCLM p v β y)
                (Measure.map (fp81s21_initGauss_synthesis p) G) ∧
              (∫ y, fp81s21_windowCoordCLM p u α y *
                    fp81s21_windowCoordCLM p v β y
                  ∂(Measure.map (fp81s21_initGauss_synthesis p) G)) =
                HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                  (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
                  (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) := by
  obtain ⟨δ26, hδ26, hδhalf, hcommon⟩ := fp81s21_initGaussIid_common p
  refine ⟨δ26, hδ26, hδhalf, ?_⟩
  intro δ hδ hδle R hγ a ha G _ hG
  obtain ⟨G', hG'prob, hG', hcov⟩ := hcommon δ hδ hδle R hγ a ha
  letI : IsProbabilityMeasure G' := hG'prob
  have heq : G = G' := fp81s21_initial_iid_gaussian_ext hG hG'
  rw [heq]
  exact hcov

#print axioms fp81s21_initial_future_supplied_covariance

end HRS.Fp81.S21

end
