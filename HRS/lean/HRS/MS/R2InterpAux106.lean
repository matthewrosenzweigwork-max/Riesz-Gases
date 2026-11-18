import HRS.MS.R2InterpAux105

/-!
# S10.2 (worker S10R), part 106 (packet M2b): the field `η_N = √N(μ_N - μ)` is admissible for the covariance measure (S10.1)

`IsR2L1F` for `s102_etaf μ X ζ` along a continuous particle path: linearity and boundedness (`S102Z`), measurability in time, and the explicit dual-norm bound
`‖η^u‖_{F_{r,P}} ≤ √N C₀ (μ_N^u(⟨x⟩^P) + μ(⟨x⟩^P))`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {Pw : ℝ}

theorem s102_dualNormE_le {r : ℕ} {z : (Euc d → ℝ) → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal) :
    dualNormE r Pw z ≤ ENNReal.ofReal M := by
  unfold dualNormE
  refine iSup_le fun f => iSup_le fun hf => ?_
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  have hw : IsR2WeightedTest r Pw f := ⟨hf1.of_le (by exact_mod_cast le_top), hf4⟩
  have h1 : ENNReal.ofReal |z f| ≤ ENNReal.ofReal M * weightedSobolevE r Pw f := by
    calc ENNReal.ofReal |z f| ≤ ENNReal.ofReal (M * (weightedSobolevE r Pw f).toReal) :=
          ENNReal.ofReal_le_ofReal (hM f hw)
      _ = ENNReal.ofReal M * weightedSobolevE r Pw f := by
          rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_toReal hf4.ne]
  calc ENNReal.ofReal |z f| / weightedSobolevE r Pw f ≤ ENNReal.ofReal M * weightedSobolevE r Pw f /
        weightedSobolevE r Pw f := by gcongr
    _ = ENNReal.ofReal M := ENNReal.mul_div_cancel_right hf3.ne' hf4.ne

/-- The explicit bound of `η_N^u` on the weighted tests. -/
def s102_Meta (C0 : ℝ) (Pw : ℝ) (μ : Measure (Euc d)) {N : ℕ} (X : EucConfig d N) : ℝ :=
  Real.sqrt N * C0 * ((N : ℝ)⁻¹ * ∑ k, jbracket (X k) ^ Pw + ∫ x, jbracket x ^ Pw ∂μ)

theorem s102_eta_bound (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (r : ℕ) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N)
    (μ : Measure (Euc d)) (hμ : Integrable (fun x => jbracket x ^ Pw) μ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (X : EucConfig d N) (f : Euc d → ℝ), IsR2WeightedTest r Pw f →
      |Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) f - HRS.Whole.pair μ f)| ≤
        s102_Meta C0 Pw μ X * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C0, hC0, hb⟩ := s102_eval_bound hd hP0 r hr
  refine ⟨C0, hC0, fun X f hf => ?_⟩
  have hE := ENNReal.toReal_nonneg (a := weightedSobolevE r Pw f)
  have hbd : ∀ x, |f x| ≤ C0 * jbracket x ^ Pw * (weightedSobolevE r Pw f).toReal := fun x => hb x f hf.1 hf.2
  have h1 : |HRS.Whole.pair (HRS.Whole.empirical X) f| ≤
      C0 * (weightedSobolevE r Pw f).toReal * ((N : ℝ)⁻¹ * ∑ k, jbracket (X k) ^ Pw) := by
    rw [HRS.Whole.pair_empirical hN, abs_mul, abs_of_nonneg (by positivity)]
    have : |∑ k, f (X k)| ≤ ∑ k, C0 * (weightedSobolevE r Pw f).toReal * jbracket (X k) ^ Pw :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => by
        calc |f (X k)| ≤ C0 * jbracket (X k) ^ Pw * (weightedSobolevE r Pw f).toReal := hbd _
          _ = _ := by ring)
    calc (N : ℝ)⁻¹ * |∑ k, f (X k)| ≤ (N : ℝ)⁻¹ * ∑ k, C0 * (weightedSobolevE r Pw f).toReal * jbracket (X k) ^ Pw :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have h2 : |HRS.Whole.pair μ f| ≤ C0 * (weightedSobolevE r Pw f).toReal * ∫ x, jbracket x ^ Pw ∂μ := by
    unfold HRS.Whole.pair
    calc |∫ x, f x ∂μ| = ‖∫ x, f x ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C0 * (weightedSobolevE r Pw f).toReal * jbracket x ^ Pw ∂μ :=
          norm_integral_le_of_norm_le (hμ.const_mul _) (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs]
            calc |f x| ≤ C0 * jbracket x ^ Pw * (weightedSobolevE r Pw f).toReal := hbd x
              _ = _ := by ring)
      _ = _ := by rw [integral_const_mul]
  unfold s102_Meta
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h3 : |HRS.Whole.pair (HRS.Whole.empirical X) f - HRS.Whole.pair μ f| ≤
      C0 * (weightedSobolevE r Pw f).toReal * ((N : ℝ)⁻¹ * ∑ k, jbracket (X k) ^ Pw + ∫ x, jbracket x ^ Pw ∂μ) := by
    calc _ ≤ |HRS.Whole.pair (HRS.Whole.empirical X) f| + |HRS.Whole.pair μ f| := abs_sub _ _
      _ ≤ _ := by linarith
  calc Real.sqrt N * |HRS.Whole.pair (HRS.Whole.empirical X) f - HRS.Whole.pair μ f|
      ≤ Real.sqrt N * (C0 * (weightedSobolevE r Pw f).toReal *
        ((N : ℝ)⁻¹ * ∑ k, jbracket (X k) ^ Pw + ∫ x, jbracket x ^ Pw ∂μ)) :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    _ = _ := by ring

end HRS.MS.R2Interp

end
