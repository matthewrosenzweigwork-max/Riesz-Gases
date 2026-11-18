import HRS.MS.Fp81S21LargeShift4

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm CbUnitBall)
open HRS.MS.R26T3

/-- A scaled-expectation envelope transfers to the cubic coefficient and residual. -/
theorem fp81s21_initial_residual_exp_bound
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {c D : ℝ} (hD : 0 ≤ D)
    (hφ : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ)))
    (hscaled : ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (r26t3_qwin R a i) (r26t3_qwin R a j)) →
        ∀ Φ : SeqL2 → ℝ, ContDiff ℝ 5 Φ →
          (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
          |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
              (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G)| ≤
            D * Real.exp (-c * a)) :
    ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (r26t3_qwin R a i) (r26t3_qwin R a j)) →
        ∀ Φ : SeqL2 → ℝ, ContDiff ℝ 5 Φ →
          (∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1) →
          |Real.sqrt N * ((∫ X, Φ (featureVec (r26t3_qwin R a)
              (r26t3_marg R N) X) ∂(r26t3_Q R N)) - ∫ z, Φ z ∂G) -
            (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
              ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
                fp81s21_initial_ellv R (r26t3_qwin R a) x,
                fp81s21_initial_ellv R (r26t3_qwin R a) x]
              ∂(r26t3_mu R 0) ∂G| ≤ 2 * D * Real.exp (-c * a) := by
  intro N hN a ha G _ hG Φ hΦ hb
  let T : ℝ := (1 / 6) * ∫ z, ∫ x, iteratedFDeriv ℝ 3 Φ z
    ![fp81s21_initial_ellv R (r26t3_qwin R a) x,
      fp81s21_initial_ellv R (r26t3_qwin R a) x,
      fp81s21_initial_ellv R (r26t3_qwin R a) x] ∂(r26t3_mu R 0) ∂G
  let S : ℕ → ℝ := fun n => Real.sqrt n *
    ((∫ X, Φ (featureVec (r26t3_qwin R a) (r26t3_marg R n) X) ∂(r26t3_Q R n)) - ∫ z, Φ z ∂G)
  have hT : |T| ≤ D * Real.exp (-c * a) := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N0, hN0⟩ := fp81s21_initial_main_l2 hδ hδh R E hγ
      (hφ ⟨a, ha⟩) (F ⟨a, ha⟩) hG ε hε
    have herr : |S (max N0 2) - T| ≤ ε := by
      simpa [S, T] using hN0 (max N0 2) (le_max_left _ _) (le_max_right _ _) hΦ hb
    have hs : |S (max N0 2)| ≤ D * Real.exp (-c * a) := by
      simpa [S] using hscaled (max N0 2) (le_max_right _ _) a ha hG Φ hΦ hb
    calc
      |T| = |S (max N0 2) - (S (max N0 2) - T)| := by congr 1 <;> ring
      _ ≤ |S (max N0 2)| + |S (max N0 2) - T| := abs_sub _ _
      _ ≤ D * Real.exp (-c * a) + ε := add_le_add hs herr
  change |S N - T| ≤ _
  calc
    _ ≤ |S N| + |T| := abs_sub _ _
    _ ≤ D * Real.exp (-c * a) + D * Real.exp (-c * a) :=
      add_le_add (by simpa [S] using hscaled N hN a ha hG Φ hΦ hb) hT
    _ = 2 * D * Real.exp (-c * a) := by ring

#print axioms fp81s21_initial_residual_exp_bound
end HRS.Fp81.S21
end
