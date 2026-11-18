import HRS.MS.Fp81S21FRUniform3
import HRS.MS.Fp81S21UnifLinSeries5
import HRS.MS.Fp81S21RankKernel

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- A finite-rank rate common to all nonnegative qwin shifts and matched Gaussian laws. -/
theorem fp81s21_initial_FR_uniform_qwin (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ E : InitialSteinEnv R, ∀ F : fp81s21_CompatPotentialFamily R,
        ∀ D : fp81s21_RankKernel p.d,
        ∃ KFR : ℝ, 0 ≤ KFR ∧
          ∀ a : Set.Ici (0 : ℝ), ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
            IsCenteredGaussianSeq G (fun l q =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R (a : ℝ) l) (r26t3_qwin R (a : ℝ) q)) →
            ∀ N : ℕ, 2 ≤ N → ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
              |fp81s21_initial_Bterm R (r26t3_qwin R (a : ℝ)) N D.kernel ψ -
                (1 / 2) * ∑' l, ∑' q,
                  fp81s21_initial_Qk R (r26t3_qwin R (a : ℝ)) D.kernel l q *
                    ∫ z, S99.pd (S99.pd ψ l) q z ∂G| ≤ KFR / Real.sqrt N := by
  obtain ⟨δq, hδq, hδqh, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δs, hδs, hδsh, hfeatureSum⟩ := fp81s21_qwin_featureSum_uniform p
  let δ0 := min δq δs
  have hδ0 : 0 < δ0 := lt_min hδq hδs
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left δq δs).trans hδqh
  refine ⟨δ0, hδ0, hδ0h, fun δ hδ hδle R E F D => ?_⟩
  have hδqR : δ ≤ δq := hδle.trans (min_le_left δq δs)
  have hδsR : δ ≤ δs := hδle.trans (min_le_right δq δs)
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
  obtain ⟨K, hK, hrate⟩ := fp81s21_initial_FR_uniform hδ
    (hδle.trans hδ0h) R E hγ φ hφ F S hS0 hSum D.valid
  refine ⟨K, hK, fun a G _ hG N hN ψ hψ => ?_⟩
  simpa [φ, fp81s21_RankKernel.kernel] using hrate a hG N hN hψ

#print axioms fp81s21_initial_FR_uniform_qwin

end HRS.Fp81.S21
end
