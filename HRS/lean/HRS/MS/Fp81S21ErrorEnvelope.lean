import HRS.MS.Fp81S21GaussLaw3
import HRS.MS.Fp81S21GaussFeature
import HRS.MS.Fp81S21Skeleton

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- The O1 Gaussian at a nonnegative start, viewed as an R26-T3 realization. -/
private def fp81s21_error_reference_gaussian
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (b : ℝ) (hb : 0 ≤ b) : GaussianRealization R := by
  let G := O1.data b hb
  letI : MeasurableSpace G.Ω := G.mΩ
  letI : IsProbabilityMeasure G.P := G.hP
  refine ⟨G.Ω, G.P, G.process, ?_⟩
  intro H
  simpa [r26t3_coeff, r26t3_mu] using G.evolution H

/-- The actual errors over the particle, Gaussian, start, and test binders of
`S21eExpBound`, packaged by the corresponding R26-T3 realization records. -/
def fp81s21_errorValues
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (κ : ℝ → projTensor (Window p) 3) (N : ℕ) : Set ℝ :=
  {e | ∃ A : Particle R N, ∃ G : GaussianRealization R,
    ∃ b : ℝ, 0 ≤ b ∧ ∃ Φ : Window p → ℝ,
      Φ ∈ CbUnitBall (Window p) 5 ∧ e = r26t3_error κ A G b Φ}

/-- The actual-error supremum with zero adjoined, as required for nonnegativity. -/
noncomputable def fp81s21_errorEnvelope
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (κ : ℝ → projTensor (Window p) 3) (N : ℕ) : ℝ :=
  sSup (insert 0 (fp81s21_errorValues p R κ N))

/-- O1's mixed-moment bound controls the norm of its actual cubic tensor uniformly
over all nonnegative starts. -/
theorem fp81s21_O1_kappa_norm_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (b : ℝ) (hb : 0 ≤ b) :
    ‖fp81s21_O1_kappa O1 b‖ ≤ O1.Kb := by
  let G := O1.data b hb
  letI : MeasurableSpace G.Ω := G.mΩ
  letI : IsProbabilityMeasure G.P := G.hP
  have hnorm := HRS.MS.S21E.s21e_kappa_norm_le
    (P := G.P) (κ₀ := G.κ₀) (D := G.D) (Z := G.Zpath) (J := G.J)
    G.D_meas G.Z_meas G.J_meas G.DZZ_integrable G.JZ_integrable
  calc
    ‖fp81s21_O1_kappa O1 b‖ =
        ‖(fp81s21_O1_kappa O1 b : TensorDual (Window p) 3)‖ := rfl
    _ = ‖fp81s21_kappaValue G‖ :=
      congrArg norm (fp81s21_O1_kappa_eq O1 b hb)
    _ = ‖HRS.MS.S21E.s21eKappa G.P G.κ₀ G.D G.Zpath G.J‖ := by
      simp [fp81s21_kappaValue, G]
    _ ≤ O1.Kb := le_trans hnorm (O1.moment_bound b hb)

private theorem fp81s21_r26t3_error_le_of_kappa_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (κ : ℝ → projTensor (Window p) 3) (Kb : ℝ)
    (hKb : 0 ≤ Kb)
    (hκ : ∀ b : ℝ, 0 ≤ b → ‖κ b‖ ≤ Kb)
    (N : ℕ) (A : Particle R N) (G : GaussianRealization R)
    (b : ℝ) (hb : 0 ≤ b) (Φ : Window p → ℝ)
    (hΦ : Φ ∈ CbUnitBall (Window p) 5) :
    r26t3_error κ A G b Φ ≤ 2 * Real.sqrt N + Kb / 6 := by
  have hΦval : ∀ z : Window p, ‖Φ z‖ ≤ 1 := by
    intro z
    simpa [Real.norm_eq_abs] using HRS.abs_apply_le_of_mem hΦ z
  have hΦ3 : ∀ z : Window p, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ 1 := by
    intro z
    exact HRS.iteratedFDeriv_norm_le_of_mem hΦ (by norm_num) z
  have hIA : |∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := A.P)
      (f := fun ζ => Φ (r26t3_zetapath A b ζ)) (C := 1)
      (Filter.Eventually.of_forall fun ζ => hΦval (r26t3_zetapath A b ζ))
    simpa [Real.norm_eq_abs, Measure.real] using h
  have hIG : |∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P| ≤ 1 := by
    have h := norm_integral_le_of_norm_le_const (μ := G.P)
      (f := fun ζ => Φ (r26t3_Zpath G b ζ)) (C := 1)
      (Filter.Eventually.of_forall fun ζ => hΦval (r26t3_Zpath G b ζ))
    simpa [Real.norm_eq_abs, Measure.real] using h
  have hκ' : ‖(κ b : TensorDual (Window p) 3)‖ ≤ Kb := by
    calc
      ‖(κ b : TensorDual (Window p) 3)‖ = ‖κ b‖ := rfl
      _ ≤ Kb := hκ b hb
  have hpair : ∀ z : Window p,
      ‖(κ b : TensorDual (Window p) 3) (iteratedFDeriv ℝ 3 Φ z)‖ ≤ Kb := by
    intro z
    calc
      ‖(κ b : TensorDual (Window p) 3) (iteratedFDeriv ℝ 3 Φ z)‖ ≤
          ‖(κ b : TensorDual (Window p) 3)‖ * ‖iteratedFDeriv ℝ 3 Φ z‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Kb * 1 := mul_le_mul hκ' (hΦ3 z) (norm_nonneg _) hKb
      _ = Kb := mul_one _
  have hI3 :
      ‖∫ ζ, (κ b : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P‖ ≤ Kb := by
    have h := norm_integral_le_of_norm_le_const (μ := G.P)
      (f := fun ζ => (κ b : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ))) (C := Kb)
      (Filter.Eventually.of_forall fun ζ => hpair (r26t3_Zpath G b ζ))
    simpa [Measure.real] using h
  have hfirst :
      |Real.sqrt N * ((∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P) -
          ∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P)| ≤ 2 * Real.sqrt N := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt N * |(∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P) -
          ∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P| ≤
          Real.sqrt N * (|∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P| +
            |∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt N * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hIA hIG) (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt N := by ring
  have hthird :
      |(1 / 6 : ℝ) * ∫ ζ, (κ b : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P| ≤ Kb / 6 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)]
    have hI3' :
        |∫ ζ, (κ b : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P| ≤ Kb := by
      simpa [Real.norm_eq_abs] using hI3
    calc
      (1 / 6 : ℝ) * |∫ ζ, (κ b : TensorDual (Window p) 3)
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P| ≤ (1 / 6) * Kb :=
        mul_le_mul_of_nonneg_left hI3' (by norm_num)
      _ = Kb / 6 := by ring
  unfold r26t3_error
  calc
    |Real.sqrt N * ((∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P) -
        ∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P) -
        (1 / 6) * ∫ ζ, (κ b : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P| ≤
        |Real.sqrt N * ((∫ ζ, Φ (r26t3_zetapath A b ζ) ∂A.P) -
          ∫ ζ, Φ (r26t3_Zpath G b ζ) ∂G.P)| +
        |(1 / 6) * ∫ ζ, (κ b : TensorDual (Window p) 3)
          (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ζ)) ∂G.P| := abs_sub _ _
    _ ≤ 2 * Real.sqrt N + Kb / 6 := add_le_add hfirst hthird

private theorem fp81s21_errorValues_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (N : ℕ) (hN : 2 ≤ N) (e : ℝ)
    (he : e ∈ fp81s21_errorValues p R (fp81s21_O1_kappa O1) N) :
    e ≤ 2 * Real.sqrt N + O1.Kb / 6 := by
  rcases he with ⟨A, G, b, hb, Φ, hΦ, rfl⟩
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  let G0 : GaussianRealization R := fp81s21_error_reference_gaussian p R O1 b hb
  have htransfer := fp81s21_r26t3_error_realization_invariant
    p R G0 (fp81s21_O1_kappa O1) A G b hb Φ hΦ
  rw [htransfer]
  have hκ : ∀ b : ℝ, 0 ≤ b → ‖fp81s21_O1_kappa O1 b‖ ≤ O1.Kb :=
    fun b hb => fp81s21_O1_kappa_norm_le p R O1 b hb
  have hKb : 0 ≤ O1.Kb := by
    have h := hκ 0 le_rfl
    exact le_trans (norm_nonneg _) h
  exact fp81s21_r26t3_error_le_of_kappa_bound p R
    (fp81s21_O1_kappa O1) O1.Kb hKb hκ N A G0 b hb Φ hΦ

/-- The actual error set is bounded by the explicit particle and cubic bounds.
Arbitrary Gaussian realizations are transferred to the O1 reference at the same start. -/
theorem fp81s21_errorValues_bddAbove
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (N : ℕ) (hN : 2 ≤ N) :
    BddAbove (fp81s21_errorValues p R (fp81s21_O1_kappa O1) N) := by
  refine ⟨2 * Real.sqrt N + O1.Kb / 6, ?_⟩
  intro e he
  exact fp81s21_errorValues_le p R O1 N hN e he

/-- The envelope is nonnegative because zero belongs to the set defining its supremum. -/
theorem fp81s21_errorEnvelope_nonneg
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N := by
  unfold fp81s21_errorEnvelope
  have hbd := fp81s21_errorValues_bddAbove p R O1 N hN
  rcases hbd with ⟨M, hM⟩
  have hunion : BddAbove (insert 0
      (fp81s21_errorValues p R (fp81s21_O1_kappa O1) N)) := by
    refine ⟨max 0 M, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (hM hx).trans (le_max_right _ _)
  exact le_csSup hunion (by simp)

/-- The envelope obeys the explicit `2 * sqrt N + Kb / 6` bound. -/
theorem fp81s21_errorEnvelope_le
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (N : ℕ) (hN : 2 ≤ N) :
    fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
      2 * Real.sqrt N + O1.Kb / 6 := by
  have hκ0 : 0 ≤ O1.Kb := by
    have h := fp81s21_O1_kappa_norm_le p R O1 0 le_rfl
    exact le_trans (norm_nonneg _) h
  apply csSup_le
  · exact ⟨0, by simp⟩
  · intro x hx
    rcases hx with rfl | hx
    · positivity
    · exact fp81s21_errorValues_le p R O1 N hN x hx

/-- The skeleton's `E_finite` clause is immediate for this real-valued envelope. -/
theorem fp81s21_errorEnvelope_E_finite
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (κ : ℝ → projTensor (Window p) 3) (N : ℕ) (hN : 2 ≤ N) :
    ∃ M : ℝ, fp81s21_errorEnvelope p R κ N ≤ M :=
  ⟨fp81s21_errorEnvelope p R κ N, le_rfl⟩

#print axioms fp81s21_O1_kappa_norm_le
#print axioms fp81s21_errorValues_bddAbove
#print axioms fp81s21_errorEnvelope_nonneg
#print axioms fp81s21_errorEnvelope_le
#print axioms fp81s21_errorEnvelope_E_finite

end HRS.Fp81.S21

end
