import HRS.MS.R2InterpAux126
import HRS.MS.R2InterpAux107
import HRS.MS.R2InterpAux92

/-!
# S10.2 (worker S10S), part 127 (packet M3b): a bound of the fluctuation field on the weighted tests, uniform in `u ∈ [0,T]` along a continuous path

`|ζ_N^u f| ≤ M_ζ ‖f‖_{E_{r,P}}` with `M_ζ` independent of `u` (the constant `C₀` of the evaluation bound is independent of the measure; the empirical moment is
continuous in `u`, hence bounded on `[0,T]`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {Pw : ℝ}

theorem s102_eta_bound_unif (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (r : ℕ) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (μ : Measure (Euc d)), Integrable (fun x => jbracket x ^ Pw) μ →
      ∀ (X : EucConfig d N) (f : Euc d → ℝ), IsR2WeightedTest r Pw f →
      |Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) f - HRS.Whole.pair μ f)| ≤
        s102_Meta C0 Pw μ X * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C0, hC0, hb⟩ := s102_eval_bound hd hP0 r hr
  refine ⟨C0, hC0, fun μ hμ X f hf => ?_⟩
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


theorem s102_zf_unif (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (r : ℕ) (hr : (d : ℝ) / 2 < r) {N : ℕ} (hN : 0 < N) {T : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (hmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))))
    {Cm : ℝ} (hCm : ∀ u ∈ Icc (0 : ℝ) T,
      ∫ x, jbracket x ^ Pw ∂(HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) ≤ Cm)
    (ζ : Ω) (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ζ k) :
    ∃ M : ℝ, ∀ u ∈ Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      |s102_zf P X ζ u f| ≤ M * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C0, hC0, hb⟩ := s102_eta_bound_unif hd hP0 r hr hN
  have hj : Continuous fun z : Euc d => jbracket z ^ Pw :=
    (by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb z)).ne')
  have hg : Continuous fun u : ℝ => (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw :=
    continuous_const.mul (continuous_finsetSum _ fun k _ => hj.comp ((hcz k).comp continuous_real_toNNReal))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc (0 : ℝ) T))
  refine ⟨Real.sqrt N * C0 * (B + max Cm 0), fun u hu f hf => ?_⟩
  have h1 := hb _ (hmom u hu) (X u.toNNReal ζ) f hf
  have hE := ENNReal.toReal_nonneg (a := weightedSobolevE r Pw f)
  have hBu : (N : ℝ)⁻¹ * ∑ k, jbracket (X u.toNNReal ζ k) ^ Pw ≤ B := (le_abs_self _).trans (hB u hu)
  have hCu := (hCm u hu).trans (le_max_left Cm 0)
  have hMeta : s102_Meta C0 Pw (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) (X u.toNNReal ζ) ≤
      Real.sqrt N * C0 * (B + max Cm 0) := by
    unfold s102_Meta
    have : 0 ≤ Real.sqrt N * C0 := mul_nonneg (Real.sqrt_nonneg _) hC0.le
    nlinarith
  unfold s102_zf
  exact h1.trans (mul_le_mul_of_nonneg_right hMeta hE)

end HRS.MS.R2Interp

end
