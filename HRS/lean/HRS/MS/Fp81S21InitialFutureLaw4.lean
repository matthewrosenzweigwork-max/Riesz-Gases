import HRS.MS.Fp81S21InitialFutureLaw3

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- Every covariance-matched initial sequence Gaussian has the required
finite-dimensional synthesized window laws, under one radius for both
coupling branches. -/
theorem fp81s21_initial_future_initial_fdd (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        ∀ a : ℝ, 0 ≤ a → ∀ (G : Measure SeqL2) [IsProbabilityMeasure G],
          IsCenteredGaussianSeq G (fun j k =>
            HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
              (r26t3_qwin R a j) (r26t3_qwin R a k)) →
          ∀ (n : ℕ) (ts : Fin n → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) p.T)
            (αs : Fin n → MultiIndex p.d),
          (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (propagatorW (r26t3_coeff R) 0 (a + ts i) (oscTestFun (wholeSpaceIndex p.d) (αs i)))
            (propagatorW (r26t3_coeff R) 0 (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs j)))).PosSemidef ∧
          (Measure.map (fp81s21_initGauss_synthesis p) G).map
            (fun w : Window p => (WithLp.toLp 2 fun i => OscDual.coord
              (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin n))) =
            multivariateGaussian 0 (Matrix.of fun i j =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (propagatorW (r26t3_coeff R) 0 (a + ts i) (oscTestFun (wholeSpaceIndex p.d) (αs i)))
                (propagatorW (r26t3_coeff R) 0 (a + ts j) (oscTestFun (wholeSpaceIndex p.d) (αs j)))) := by
  obtain ⟨δ26, hδ26, hδhalf, hcov⟩ := fp81s21_initial_future_supplied_covariance p
  refine ⟨δ26, hδ26, hδhalf, ?_⟩
  intro δ hδ hδle R a ha G _ hG n ts hts αs
  have hγ : 0 < p.γ ∨ p.γ = 0 := by
    rcases eq_or_lt_of_le p.hγ with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  apply fp81s21_initial_future_synthesis_fdd p G hG.1 n ts hts αs
  intro i j
  simpa only [r26t3_U] using (hcov δ hδ hδle R hγ a ha G hG
    ⟨ts i, hts i⟩ ⟨ts j, hts j⟩ (αs i) (αs j)).2

#print axioms fp81s21_initial_future_initial_fdd

end HRS.Fp81.S21

end
