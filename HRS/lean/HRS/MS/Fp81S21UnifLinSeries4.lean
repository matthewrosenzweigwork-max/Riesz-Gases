import HRS.MS.Fp81S21UnifLinSeries3

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- Uniform smooth CLT estimate for an indexed feature family with a common feature-sum
bound. The static tilt constant is chosen once, before the family index and Gaussian. -/
theorem fp81s21_initial_clt_uniform_of_featureSum_bound
    {p : Parameters} {δ : ℝ} (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) {ι : Type} (φ : ι → ℕ → Euc p.d → ℝ)
    (hφ : ∀ i, IsSummableFeatureFamily (fp81s21_J1 p.d) (φ i))
    (S : ℝ) (hS0 : 0 ≤ S)
    (hSum : ∀ i, featureSum (fp81s21_J1 p.d) (φ i) ≤ S) :
    ∃ Kclt : ℝ, 0 ≤ Kclt ∧
      ∀ i, ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun j k =>
          HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (φ i j) (φ i k)) →
        ∀ N : ℕ, 2 ≤ N → ∀ {H : SeqL2 → ℝ}, S99.Bd 2 H →
          Integrable (fun X : EucConfig p.d N =>
            H (featureVec (φ i) (r26t3_marg R N) X)) (r26t3_Q R N) ∧
          Integrable H G ∧
          |∫ X, H (featureVec (φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N) -
            ∫ z, H z ∂G| ≤ Kclt / Real.sqrt N := by
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith [p.hs]
  have hJ : (p.d : ℝ) / 2 + 2 < (fp81s21_J1 p.d : ℝ) := by
    unfold fp81s21_J1
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  obtain ⟨Cst, Cs, hCst, hCs, hclass⟩ :=
    HRS.MS.S21.s21u_tiltClass p.hd p.hs0 hsd p.ha p.hβ hγ
      (J := fp81s21_J1 p.d) hJ (εstar := δ) hδh
  have hρ0 : R.ρ 0 = perturbedDensity R.ρβ R.ε R.ψ := R.resulting.init
  have hμ : r26t3_mu R 0 =
      HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ) := by
    simp [r26t3_mu, hρ0]
  let Kclt : ℝ := Cst * (S + S ^ 2)
  have hKclt0 : 0 ≤ Kclt := by
    dsimp [Kclt]
    positivity
  refine ⟨Kclt, hKclt0, fun i {G} [IsProbabilityMeasure G] hG N hN H hH => ?_⟩
  have hG' : IsCenteredGaussianSeq G (fun j k =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ)) p.γ
        ((φ i) j) ((φ i) k)) := by
    simpa only [← hμ] using hG
  have hStatic := hclass R.ρβ R.thermal R.ε R.ψ R.admissible N hN
  have hmod :
      HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.γ
          (HRS.Whole.withDensityReal (perturbedDensity R.ρβ R.ε R.ψ)) = r26t3_Q R N := by
    simp [r26t3_Q, r26t3_mu, hρ0]
  have hstat : StaticFieldConclusion p.d p.s N (r26t3_Q R N)
      (r26t3_marg R N) (fp81s21_J1 p.d) (φ i) G Cst := by
    simpa only [hmod, r26t3_marg] using hStatic.static (φ i) (hφ i) G hG'
  obtain ⟨-, -, -, hcomp⟩ := hstat
  have hF1 : ∀ z, ‖fderiv ℝ H z‖ ≤ 1 := fun z => hH.fderiv_le z
  have hF2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ 1 := fun z =>
    hH.2 2 le_rfl z
  obtain ⟨hIntQ, hIntG, hDiff⟩ := hcomp H hH.1 1 1 hF1 hF2
  have hN1 : 1 ≤ N := by omega
  have hδN : HRS.deltaN p.d p.s N = 1 / (N : ℝ) := by
    have hmul := HRS.MS.R2Mt.s92_mul_deltaN (d := p.d) (N := N) p.hs hN
    field_simp
    linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrtδ : Real.sqrt (HRS.deltaN p.d p.s N) = 1 / Real.sqrt N := by
    rw [hδN, Real.sqrt_div (by norm_num), Real.sqrt_one]
  let x : ℝ := featureSum (fp81s21_J1 p.d) (φ i)
  have hx0 : 0 ≤ x := by
    dsimp [x, featureSum]
    exact tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hxS : x ≤ S := hSum i
  have hx2 : x ^ 2 ≤ S ^ 2 := by
    have hmul := mul_le_mul hxS hxS hx0 hS0
    nlinarith [hmul]
  have hplus : x + x ^ 2 ≤ S + S ^ 2 := add_le_add hxS hx2
  have hrate :
      |∫ X, H (featureVec (φ i) (r26t3_marg R N) X) ∂(r26t3_Q R N) -
        ∫ z, H z ∂G| ≤ Kclt * Real.sqrt (HRS.deltaN p.d p.s N) := by
    calc
      _ ≤ Cst * Real.sqrt (HRS.deltaN p.d p.s N) * (x + x ^ 2) := by
        simpa [x, mul_assoc] using hDiff
      _ ≤ Cst * Real.sqrt (HRS.deltaN p.d p.s N) * (S + S ^ 2) :=
        mul_le_mul_of_nonneg_left hplus
          (mul_nonneg hCst (Real.sqrt_nonneg _))
      _ = Kclt * Real.sqrt (HRS.deltaN p.d p.s N) := by
        dsimp [Kclt]
        ring
  refine ⟨hIntQ, hIntG, ?_⟩
  rw [hsqrtδ] at hrate
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrate

#print axioms fp81s21_initial_clt_uniform_of_featureSum_bound

end HRS.Fp81.S21

end
