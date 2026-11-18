import HRS.MS.Fp81S21LargeShift5
import HRS.MS.Fp81S21QwinUniform

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole
open HRS (Euc MemCb cbNorm CbUnitBall)
open HRS.MS.R26T3

/-- Uniform exponential control of the large-shift static Edgeworth residual. -/
theorem fp81s21_initial_large_shift (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ7 : ℝ, 0 < δ7 ∧ δ7 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ7 → ∀ R : Trajectory p δ,
        ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
          ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
            ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
              IsCenteredGaussianSeq G (fun i j =>
                HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
                  (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
              ∀ Φ : SeqL2 → ℝ, Φ ∈ CbUnitBall SeqL2 5 →
                |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
                    (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
                  (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
                    ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                      fp81s21_initial_ellv R (r26t3_qwin R a) x,
                      fp81s21_initial_ellv R (r26t3_qwin R a) x]
                    ∂(r26t3_mu R 0) ∂G| ≤ C * Real.exp (-c * a) := by
  obtain ⟨δc, hδc, hδch, hc⟩ := fp81s21_compatible_qwin_potentials p hγ
  obtain ⟨δq, hδq, hδqh, hq⟩ := fp81s21_qwin_uniform p
  let δ7 := min δc δq
  have hδ7 : 0 < δ7 := lt_min hδc hδq
  have hδ7h : δ7 ≤ 1 / 2 := (min_le_left δc δq).trans hδch
  refine ⟨δ7, hδ7, hδ7h, fun δ hδ hδle R => ?_⟩
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ7h
  obtain ⟨K, Cχ, c, hK, hCχ, hcpos, F, hFK, hdecay⟩ :=
    hc δ hδ (hδle.trans (min_le_left δc δq)) R
  obtain ⟨Cwin, hCwin, hwin⟩ := hq δ hδ (hδle.trans (min_le_right δc δq)) R
  let E : InitialSteinEnv R := Classical.choice (initialSteinEnv_exists hδ hδhalf R hγ)
  have hφ : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)) := by
    intro a
    simpa [r26t3_J, fp81s21_J1] using (hwin a a.2).1
  have hbound : ∀ a : Set.Ici (0 : ℝ), ∀ k : ℕ,
      cbNorm (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ) k) ≤
        Cwin * r26t3_feature_weight p.d k := by
    intro a k
    simpa [r26t3_J, fp81s21_J1] using (hwin a a.2).2 k
  obtain ⟨D, hD, hscaled⟩ := fp81s21_initial_scaled_expectation_exp_bound
    hδ hδhalf R E hγ F hCχ hCwin hdecay hφ hbound
  refine ⟨2 * D, c, by positivity, hcpos, ?_⟩
  intro N hN a ha G _ hG Φ hΦ
  exact fp81s21_initial_residual_exp_bound hδ hδhalf R E hγ F hD hφ hscaled
    N hN a ha hG Φ hΦ.1 (fun i hi z => HRS.iteratedFDeriv_norm_le_of_mem hΦ hi z)

#print axioms fp81s21_initial_large_shift
end HRS.Fp81.S21
end
