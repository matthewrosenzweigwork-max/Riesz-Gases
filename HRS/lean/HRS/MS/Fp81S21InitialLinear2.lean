import HRS.MS.Fp81S21InitialLinear

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS.Whole
open HRS (Euc cbNorm MemCb)
open HRS.MS.R26T3

/-!
## SOL31 packet 24a: leading comparison and `s99_clt`

Exact thermal source (`R2SeAux9:33`): for `J > d/2 + 2`, a summable `J`-feature family
and a centered Gaussian `G` with covariance
`susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (φ i) (φ j)`,
`s99_clt` chooses `K ≥ 0` before `N,F`; for every `N ≥ 2` and `F ∈ Bd 2`, both
`F(featureVec φ (s46_nu N) ·)` under `s46_P N` and `F` under `G` are integrable and
their expectation difference is at most `K / sqrt N`.

Dependencies: the `Bd 2` expectation comparison is **generic** in the S4.5
`StaticFieldConclusion`; **already ported** are the actual-law `InitialSteinEnv`, trajectory
initial-density identity, and S47 static setup; the S47 smooth comparison is applied through
`S21.s21u_tiltClass` at the trajectory's actual perturbation. No thermal Euler equation is
used. The identity `deltaN = 1/N` uses `p.hs` and `N ≥ 2`.
-/

/-- The S99 smooth feature comparison at the actual initial law, via S47's static-field
conclusion. The comparison constant is selected before `N` and the test. -/
theorem fp81s21_initial_clt
    {p : Parameters} {δ : ℝ} (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ (φ i) (φ j))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ {F : SeqL2 → ℝ}, S99.Bd 2 F →
      Integrable (fun X : EucConfig p.d N =>
        F (featureVec φ (r26t3_marg R N) X)) (r26t3_Q R N) ∧
      Integrable F G ∧
      |∫ X, F (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) -
        ∫ z, F z ∂G| ≤ K / Real.sqrt N := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith [p.hs]
  have hJ : (p.d : ℝ) / 2 + 2 < (fp81s21_J1 p.d : ℝ) := by
    unfold fp81s21_J1
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  obtain ⟨Cst, Cs, hCst, hCs, hclass⟩ :=
    HRS.MS.S21.s21u_tiltClass p.hd p.hs0 hsd p.ha p.hβ hγ (J := fp81s21_J1 p.d) hJ
      (εstar := δ) hδh
  have hρ0 : R.ρ 0 = perturbedDensity R.ρβ R.ε R.ψ := R.resulting.init
  have hμ : r26t3_mu R 0 =
      HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ) := by
    simp [r26t3_mu, hρ0]
  have hG' : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ)) p.γ
        (φ i) (φ j)) := by
    simpa only [← hμ] using hG
  let K : ℝ := Cst * (featureSum (fp81s21_J1 p.d) φ +
    featureSum (fp81s21_J1 p.d) φ ^ 2)
  refine ⟨K, ?_, fun N hN F hF => ?_⟩
  · have hS0 : 0 ≤ featureSum (fp81s21_J1 p.d) φ :=
      tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
    positivity
  have hN1 : 1 ≤ N := by omega
  have hStatic := hclass R.ρβ R.thermal R.ε R.ψ R.admissible N hN
  have hmod :
      HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.γ
          (HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ)) = r26t3_Q R N := by
    simp [r26t3_Q, r26t3_mu, hρ0]
  have hstat : StaticFieldConclusion p.d p.s N (r26t3_Q R N)
      (r26t3_marg R N) (fp81s21_J1 p.d) φ G Cst := by
    simpa only [hmod, r26t3_marg] using hStatic.static φ hφ G hG'
  obtain ⟨-, -, -, hcomp⟩ := hstat
  have hF1 : ∀ z, ‖fderiv ℝ F z‖ ≤ 1 := fun z => hF.fderiv_le z
  have hF2 : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ 1 := fun z => hF.2 2 le_rfl z
  obtain ⟨hIntQ, hIntG, hDiff⟩ := hcomp F hF.1 1 1 hF1 hF2
  have hδ : HRS.deltaN p.d p.s N = 1 / (N : ℝ) := by
    have hmul := HRS.MS.R2Mt.s92_mul_deltaN (d := p.d) (N := N) p.hs hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    field_simp
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : Real.sqrt (HRS.deltaN p.d p.s N) = 1 / Real.sqrt N := by
    rw [hδ, Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hS0 : 0 ≤ featureSum (fp81s21_J1 p.d) φ :=
    tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hrate : |∫ X, F (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) -
      ∫ z, F z ∂G| ≤ K * Real.sqrt (HRS.deltaN p.d p.s N) := by
    calc |∫ X, F (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N) -
          ∫ z, F z ∂G| ≤
        Cst * Real.sqrt (HRS.deltaN p.d p.s N) *
          (featureSum (fp81s21_J1 p.d) φ + featureSum (fp81s21_J1 p.d) φ ^ 2) := by
            simpa only [mul_one] using hDiff
      _ = K * Real.sqrt (HRS.deltaN p.d p.s N) := by dsimp [K]; ring
  refine ⟨hIntQ, hIntG, ?_⟩
  rw [hsqrt] at hrate
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrate

#print axioms fp81s21_initial_clt

end HRS.Fp81.S21

end
