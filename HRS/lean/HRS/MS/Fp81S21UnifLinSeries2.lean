import HRS.MS.Fp81S21UnifLinSeries

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

/-- A common `Ylin` rate and common `InitialFamData.K` bound give one coefficient rate
constant before the family index, any supplied covariance-matched Gaussian, and all coefficient
tests and indices. The shift-specific producer of the common `Ylin` rate is separate. -/
theorem fp81s21_initial_A_rate_uniform_of_common_Ylin
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {ι : Type} (φ : ι → ℕ → Euc p.d → ℝ)
    (hφ : ∀ i, IsSummableFeatureFamily (fp81s21_J1 p.d) (φ i))
    (F : ∀ i, InitialFamData R (φ i))
    (K KL : ℝ) (hK0 : 0 ≤ K) (hKL0 : 0 ≤ KL)
    (hFK : ∀ i, (F i).K ≤ K)
    (hYlin : ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
      IsCenteredGaussianSeq G (fun j k =>
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (φ i j) (φ i k)) →
      ∀ N : ℕ, 2 ≤ N → ∀ {w : Euc p.d → ℝ},
        MemCb (fp81s21_k0 p.d) w → ∀ {ψ : SeqL2 → ℝ}, S99.Bd 3 ψ →
        |(∫ X, s45_Yi N w (HRS.Whole.pair (r26t3_marg R N) w) X *
            ψ (featureVec (φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N)) -
          ∑' m, fp81s21_initial_kap (R := R) w (φ i) m *
            ∫ z, S99.pd ψ m z ∂G| ≤
          KL * cbNorm (fp81s21_k0 p.d) w / Real.sqrt N) :
    ∃ KA : ℝ, 0 ≤ KA ∧
      KA = (((((fp81s21_k0 p.d : ℝ) + 1) * 2 ^ fp81s21_k0 p.d) *
        (p.γ⁻¹ * K)) * (KL + E.Cs * ((fp81s21_k0 p.d : ℝ) + 1))) ∧
      ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun j k =>
          HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (φ i j) (φ i k)) →
        ∀ N : ℕ, 2 ≤ N → ∀ f : SeqL2 → ℝ, S99.SteinCl f → ∀ q : ℕ × ℕ,
          |fp81s21_initial_Aterm (F i) N f q -
              fp81s21_initial_Alim (F i) G f q| ≤
            KA * (cbNorm (fp81s21_J1 p.d) (φ i q.1) *
              cbNorm (fp81s21_J1 p.d) (φ i q.2)) / Real.sqrt N := by
  let J : ℕ := fp81s21_k0 p.d
  let Kw : ℝ := ((J : ℝ) + 1) * 2 ^ J * (p.γ⁻¹ * K)
  let KA : ℝ := Kw * (KL + E.Cs * ((J : ℝ) + 1))
  have hCs : 0 ≤ E.Cs := E.Cs_nonneg
  have hKA0 : 0 ≤ KA := by
    dsimp [KA, Kw]
    positivity
  refine ⟨KA, hKA0, rfl, ?_⟩
  intro i G hGprob hG N hN f hf q
  letI : IsProbabilityMeasure G := hGprob
  obtain ⟨KAi, hKAi0, hKAieq, hA⟩ :=
    fp81s21_initial_A_rate_from_common_Ylin hδ hδh R E hγ
      (φ := φ i) (hφ i) (F i) (G := G) hG K KL hK0 (hFK i) hKL0 (hYlin i hG)
  have hA' := hA N hN f hf q
  rw [hKAieq] at hA'
  simpa [KA, Kw, J] using hA'

#print axioms fp81s21_initial_A_rate_uniform_of_common_Ylin

end HRS.Fp81.S21

end
