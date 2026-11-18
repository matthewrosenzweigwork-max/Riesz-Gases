import HRS.MS.Fp81S21CompatPotentials
import HRS.MS.Fp81S21UnifLinSeries4

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- The positive-γ coefficient rate is uniform over all nonnegative shifts for the compatible
qwin potential family. The single `KA` is chosen before the shift, supplied Gaussian, `N`, test,
and coefficient indices. -/
theorem fp81s21_initial_A_rate_uniform (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ K C c : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧
          ∃ F : fp81s21_CompatPotentialFamily R,
            (∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K) ∧
            (∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
              HasCbBound (fp81s21_k0 p.d)
                (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
                (gradient ((F a).χ j))) ∧
            ∃ KL : ℝ, 0 ≤ KL ∧
              ∃ KA : ℝ, 0 ≤ KA ∧
                ∀ a : Set.Ici (0 : ℝ), ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
                  IsCenteredGaussianSeq G (fun i j =>
                    HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
                      (r26t3_mu R 0) p.γ
                      (r26t3_qwin R (a : ℝ) i) (r26t3_qwin R (a : ℝ) j)) →
                  ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ, S99.SteinCl f →
                    ∀ q : ℕ × ℕ,
                      |fp81s21_initial_Aterm (F a) N f q -
                          fp81s21_initial_Alim (F a) G f q| ≤
                        KA * (cbNorm (fp81s21_J1 p.d)
                          (r26t3_qwin R (a : ℝ) q.1) *
                          cbNorm (fp81s21_J1 p.d)
                            (r26t3_qwin R (a : ℝ) q.2)) / Real.sqrt N := by
  obtain ⟨δc, hδc, hδchalf, hcompat⟩ :=
    fp81s21_compatible_qwin_potentials p hγ
  obtain ⟨δq, hδq, hδqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δs, hδs, hδshalf, hfeatureSum⟩ :=
    fp81s21_qwin_featureSum_uniform p
  let δ0 : ℝ := min δc (min δq δs)
  have hδ0 : 0 < δ0 := lt_min hδc (lt_min hδq hδs)
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left δc (min δq δs)).trans hδchalf
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  have hδcR : δ ≤ δc := hδle.trans (min_le_left δc (min δq δs))
  have hδqR : δ ≤ δq :=
    hδle.trans ((min_le_right δc (min δq δs)).trans (min_le_left δq δs))
  have hδsR : δ ≤ δs :=
    hδle.trans ((min_le_right δc (min δq δs)).trans (min_le_right δq δs))
  obtain ⟨K, C, c, hK0, hC0, hc, F, hFK, hFdecay⟩ :=
    hcompat δ hδ hδcR R
  obtain ⟨Cq, hCq, hq⟩ := hqwin δ hδ hδqR R
  obtain ⟨Cs, hCs, hfsum⟩ := hfeatureSum δ hδ hδsR R
  let φ : Set.Ici (0 : ℝ) → ℕ → Euc p.d → ℝ :=
    fun a j => r26t3_qwin R (a : ℝ) j
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := rfl
  have hφ : ∀ a, IsSummableFeatureFamily (fp81s21_J1 p.d) (φ a) := by
    intro a
    have hh := (hq a.1 a.2).1
    simpa [φ, hJd] using hh
  let S : ℝ := Cs * (∑' j : ℕ, r26t3_feature_weight p.d j)
  have hweight0 : ∀ j, 0 ≤ r26t3_feature_weight p.d j := by
    intro j
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact mul_nonneg hCs (tsum_nonneg hweight0)
  have hSum : ∀ a, featureSum (fp81s21_J1 p.d) (φ a) ≤ S := by
    intro a
    have hh := hfsum a.1 a.2
    simpa [φ, hJd, S] using hh
  have hEne : Nonempty (InitialSteinEnv R) :=
    initialSteinEnv_exists hδ (hδle.trans hδ0half) R hγ
  let E : InitialSteinEnv R := Classical.choice hEne
  obtain ⟨Kclt, hKclt, hCLT⟩ :=
    fp81s21_initial_clt_uniform_of_featureSum_bound
      (p := p) (δ := δ) (hδle.trans hδ0half) R hγ φ hφ S hS0 hSum
  obtain ⟨KL, hKL, hYlin⟩ :=
    fp81s21_initial_Ylin_uniform_of_common_CLT
      hδ (hδle.trans hδ0half) R E hγ φ hφ F S hS0 hSum
      Kclt hKclt hCLT
  obtain ⟨KA, hKA0, _, hA⟩ :=
    fp81s21_initial_A_rate_uniform_of_common_Ylin
      hδ (hδle.trans hδ0half) R E hγ φ hφ F K KL hK0 hKL hFK hYlin
  refine ⟨K, C, c, hK0, hC0, hc, F, hFK, hFdecay, KL, hKL,
    KA, hKA0, ?_⟩
  intro a G hGprob hG N hN f hf q
  letI : IsProbabilityMeasure G := hGprob
  exact hA a hG N hN f hf q

#print axioms fp81s21_initial_A_rate_uniform

end HRS.Fp81.S21

end
