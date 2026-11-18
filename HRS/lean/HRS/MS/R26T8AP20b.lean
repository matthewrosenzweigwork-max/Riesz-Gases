import HRS.MS.R26T8AT5

/-!
# S8.2 local Newton layer, packet T8A.P20b: linearity of the fixed finite parametrix and unique remainder extension (Pro contract verbatim)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_parametrix_linear (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f g : Euc d → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : TestBound (testOrder d) A f) (hg : TestBound (testOrder d) B g) (c : ℝ) :
    let C0 := critCoeff d a beta rho
    let mu := HRS.Whole.withDensityReal rho
    r26t8a_parametrixZero C0 mu chi (f + c • g) =
      r26t8a_parametrixZero C0 mu chi f + c • r26t8a_parametrixZero C0 mu chi g ∧
    r26t8a_remainder C0 mu chi (f + c • g) =
      r26t8a_remainder C0 mu chi f + c • r26t8a_remainder C0 mu chi g ∧
    (∀ b : ℝ, r26t8a_parametrixZero C0 mu chi (fun _ => b) = 0 ∧
      r26t8a_remainder C0 mu chi (fun _ => b) = 0) := by
  intro C0 mu
  have hAB : 0 ≤ A + |c| * B := by positivity
  have hfg := r26t8a_T5_testBound_lin hf hg c
  refine ⟨?_, ?_, ?_⟩
  · funext x y
    by_cases hxy : x = y
    · simp [r26t8a_parametrixZero, hxy]
    · simp only [r26t8a_parametrixZero, if_neg hxy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact r26t8a_T5_parametrix_lin hd a beta ha hbeta chi hchi rho hrho hA hB hf hg c hxy
  · obtain ⟨c1, -, u1⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho hA hf
    obtain ⟨c2, -, u2⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho hB hg
    obtain ⟨-, e1, -⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho hA hf
    obtain ⟨-, e2, -⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho hB hg
    obtain ⟨-, -, u3⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho hAB hfg
    have hcont : Continuous (Function.uncurry (r26t8a_remainder C0 mu chi f + c • r26t8a_remainder C0 mu chi g)) := by
      have : Function.uncurry (r26t8a_remainder C0 mu chi f + c • r26t8a_remainder C0 mu chi g) =
          Function.uncurry (r26t8a_remainder C0 mu chi f) + c • Function.uncurry (r26t8a_remainder C0 mu chi g) := rfl
      rw [this]
      exact c1.continuous.add (c2.continuous.const_smul c)
    exact (u3 _ hcont (fun x y hxy => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1 x y hxy, e2 x y hxy]
      exact (r26t8a_T4_term_lin hd a beta ha hbeta chi hchi rho hrho hA hB hf hg c _ le_rfl x y hxy).symm)).symm
  · intro b
    have hzero : ∀ j : ℕ, r26t8a_parametrixTerm C0 mu chi (fun _ => b) j = fun _ _ => 0 := by
      intro j
      induction j with
      | zero =>
        funext x y
        have e : hSource (fun _ : Euc d => b) = fun _ _ => 0 := by
          funext x y
          simp [hSource, commutatorKernel, gradient]
        show HSource mu (fun _ => b) x y = 0
        unfold HSource
        rw [e]
        simp [r2CenterKernel]
      | succ j ih =>
        have e : r26t8a_parametrixTerm C0 mu chi (fun _ => b) (j + 1) =
            newtonDefect C0 mu chi (r26t8a_parametrixTerm C0 mu chi (fun _ => b) j) :=
          Function.iterate_succ_apply' _ _ _
        rw [e, ih]
        funext x y
        have hl : localNewton mu C0.ν chi (fun _ _ : Euc d => (0 : ℝ)) = fun _ _ => 0 := by
          funext u v
          simp [localNewton, rawNewton, midPair, r2CenterKernel]
        show (0 : ℝ) + pairA C0 mu (localNewton mu C0.ν chi (fun _ _ : Euc d => (0 : ℝ))) x y = 0
        rw [hl, r26t8a_V3_pairA_zero]
        simp
    have hT0 : TestBound (testOrder d) 0 (fun _ : Euc d => b) :=
      ⟨contDiff_const, fun j hj _ x => by
        rw [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]; simp⟩
    refine ⟨?_, ?_⟩
    · funext x y
      by_cases hxy : x = y
      · simp [r26t8a_parametrixZero, hxy]
      · simp only [r26t8a_parametrixZero, if_neg hxy]
        unfold r26t8a_parametrix
        simp only [Finset.sum_apply, hzero]
        have hl : localNewton mu C0.ν chi (fun _ _ : Euc d => (0 : ℝ)) = fun _ _ => 0 := by
          funext u v
          simp [localNewton, rawNewton, midPair, r2CenterKernel]
        simp [hl]
    · obtain ⟨-, -, u⟩ := r26t8a_T5_remainder_spec hd a beta ha hbeta chi hchi rho hrho le_rfl hT0
      have hc : Continuous (Function.uncurry (fun _ _ : Euc d => (0 : ℝ))) := continuous_const
      exact (u _ hc (fun x y _ => by rw [hzero])).symm

end HRS.MS.R26T8A
