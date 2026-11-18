import HRS.MS.Fp81S21InitialMoments
import HRS.MS.S21F_S06

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS (Euc MemCb cbNorm)
open HRS.Whole
open HRS.MS.R26T3

/-- Initial-law `T_L2`: centering at the reference law adds the S06 marginal bias
to the exactly centered `Y_L2` statistic. -/
theorem fp81s21_initial_T_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B →
      ∀ u : Euc p.d → ℝ, Measurable u → (∀ x, |u x| ≤ B) →
        Integrable (fun X : EucConfig p.d N =>
          (HRS.Whole.pair (HRS.Whole.empirical X) u -
            HRS.Whole.pair (r26t3_mu R 0) u) ^ 2) (r26t3_Q R N) ∧
        ∫ X, (HRS.Whole.pair (HRS.Whole.empirical X) u -
          HRS.Whole.pair (r26t3_mu R 0) u) ^ 2 ∂(r26t3_Q R N) ≤
            (K * B) ^ 2 / (N : ℝ) := by
  obtain ⟨KY, hKY, hY⟩ := fp81s21_initial_Y_L2 hδ hδh E hγ
  obtain ⟨C, hC, hstatic⟩ := r26t3_static_scalar hδ hδh R hγ
  have hKarg : 0 ≤ 2 * KY ^ 2 + C ^ 2 := by positivity
  refine ⟨Real.sqrt (2 * KY ^ 2 + C ^ 2), Real.sqrt_nonneg _,
    fun N hN B hB u hu hub => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hν : IsProbabilityMeasure (r26t3_marg R N) := by
    change IsProbabilityMeasure (HRS.Whole.firstMarginal (r26t3_Q R N))
    exact S99.s99_nu_prob hN1
  letI : IsProbabilityMeasure (r26t3_marg R N) := hν
  have hYpair := hY N hN B hB u hu hub
  let y : EucConfig p.d N → ℝ := fun X =>
    s45_Yi N u (HRS.Whole.pair (r26t3_marg R N) u) X
  let b : ℝ := HRS.Whole.pair (r26t3_marg R N) u -
    HRS.Whole.pair (r26t3_mu R 0) u
  let z : EucConfig p.d N → ℝ := fun X =>
    HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair (r26t3_mu R 0) u
  have hymeas : Measurable y := by
    dsimp [y, s45_Yi]
    exact measurable_const.mul
      ((S45.s45_measurable_pair_empirical hN1 hu).sub measurable_const)
  have hyint : Integrable (fun X => y X ^ 2) (r26t3_Q R N) := by
    simpa [y] using hYpair.1
  have hzmeas : Measurable z := by
    dsimp [z]
    exact (S45.s45_measurable_pair_empirical hN1 hu).sub measurable_const
  have hzbound : ∀ X, |z X| ≤ 2 * B := by
    intro X
    dsimp [z]
    have hμu : |HRS.Whole.pair (r26t3_mu R 0) u| ≤ B :=
      HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hub x)
    calc |HRS.Whole.pair (HRS.Whole.empirical X) u -
          HRS.Whole.pair (r26t3_mu R 0) u|
        ≤ |HRS.Whole.pair (HRS.Whole.empirical X) u| +
          |HRS.Whole.pair (r26t3_mu R 0) u| := abs_sub _ _
      _ ≤ B + B := add_le_add (S45.s45_abs_pair_empirical_le hN1 hub X) hμu
      _ = 2 * B := by ring
  have hzint : Integrable (fun X => z X ^ 2) (r26t3_Q R N) := by
    refine Integrable.of_bound (hzmeas.pow_const 2).aestronglyMeasurable
      ((2 * B) ^ 2) ?_
    filter_upwards with X
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hzbound X) 2
  have hbias := (hstatic N hN).2 u hu B hub
  have hdecomp : ∀ X, z X = y X / Real.sqrt N + b := by
    intro X
    dsimp [z, y, b, s45_Yi]
    have hsqrt : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
    field_simp [hsqrt]
    ring
  have hsqrt2 : (Real.sqrt N) ^ 2 = (N : ℝ) := Real.sq_sqrt hN0.le
  have hpoint : ∀ X, z X ^ 2 ≤ (2 / (N : ℝ)) * y X ^ 2 + 2 * b ^ 2 := by
    intro X
    rw [hdecomp X]
    have hdiv : (y X / Real.sqrt N) ^ 2 = y X ^ 2 / (N : ℝ) := by
      rw [div_pow, hsqrt2]
    have heq : 2 * (y X / Real.sqrt N) ^ 2 = (2 / (N : ℝ)) * y X ^ 2 := by
      rw [hdiv]
      ring
    nlinarith [sq_nonneg (y X / Real.sqrt N - b)]
  have hRhsInt : Integrable
      (fun X => (2 / (N : ℝ)) * y X ^ 2 + 2 * b ^ 2) (r26t3_Q R N) :=
    (hyint.const_mul (2 / (N : ℝ))).add (integrable_const (μ := r26t3_Q R N) _)
  have hmono := integral_mono hzint hRhsInt (fun X => hpoint X)
  have hcalc :
      ∫ X, (2 / (N : ℝ)) * y X ^ 2 + 2 * b ^ 2 ∂(r26t3_Q R N) =
        (2 / (N : ℝ)) * ∫ X, y X ^ 2 ∂(r26t3_Q R N) + 2 * b ^ 2 := by
    rw [integral_add (hyint.const_mul (2 / (N : ℝ)))
      (integrable_const (μ := r26t3_Q R N) _), integral_const_mul]
    simp
  rw [hcalc] at hmono
  have hy2 := hYpair.2
  have hyterm :
      (2 / (N : ℝ)) * ∫ X, y X ^ 2 ∂(r26t3_Q R N) ≤
        2 * KY ^ 2 * B ^ 2 / (N : ℝ) := by
    calc (2 / (N : ℝ)) * ∫ X, y X ^ 2 ∂(r26t3_Q R N)
        ≤ (2 / (N : ℝ)) * (KY * B) ^ 2 :=
          mul_le_mul_of_nonneg_left hy2 (by positivity)
      _ = 2 * KY ^ 2 * B ^ 2 / (N : ℝ) := by ring
  have hnratio : (2 : ℝ) / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    apply (div_le_div_iff₀ (sq_pos_of_pos hN0) hN0).2
    nlinarith [hN2]
  have hbterm : 2 * b ^ 2 ≤ C ^ 2 * B ^ 2 / (N : ℝ) := by
    have hbabs : |b| ≤ C * B / (N : ℝ) := by
      simpa [b] using hbias
    have hb2 : b ^ 2 ≤ (C * B / (N : ℝ)) ^ 2 := by
      calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
        _ ≤ (C * B / (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hbabs 2
    calc 2 * b ^ 2 ≤ 2 * (C * B / (N : ℝ)) ^ 2 := by nlinarith
      _ = C ^ 2 * B ^ 2 * (2 / (N : ℝ) ^ 2) := by ring
      _ ≤ C ^ 2 * B ^ 2 * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hnratio (by positivity)
      _ = C ^ 2 * B ^ 2 / (N : ℝ) := by ring
  have harg : 0 ≤ 2 * KY ^ 2 + C ^ 2 := hKarg
  refine ⟨hzint, ?_⟩
  calc ∫ X, z X ^ 2 ∂(r26t3_Q R N)
      ≤ (2 / (N : ℝ)) * ∫ X, y X ^ 2 ∂(r26t3_Q R N) + 2 * b ^ 2 := hmono
    _ ≤ 2 * KY ^ 2 * B ^ 2 / (N : ℝ) + C ^ 2 * B ^ 2 / (N : ℝ) :=
      add_le_add hyterm hbterm
    _ = (2 * KY ^ 2 + C ^ 2) * B ^ 2 / (N : ℝ) := by ring
    _ = (Real.sqrt (2 * KY ^ 2 + C ^ 2) * B) ^ 2 / (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt harg]

/-- Initial-law `T_L1`: the S99 absolute empirical fluctuation bound follows
from `T_L2` by Cauchy–Schwarz under the probability law. -/
theorem fp81s21_initial_T_L1
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    {R : Trajectory p δ} (E : InitialSteinEnv R) (hγ : 0 < p.γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ B : ℝ, 0 ≤ B →
      ∀ u : Euc p.d → ℝ, Measurable u → (∀ x, |u x| ≤ B) →
        ∫ X, |HRS.Whole.pair (HRS.Whole.empirical X) u -
          HRS.Whole.pair (r26t3_mu R 0) u| ∂(r26t3_Q R N) ≤
            K * B / Real.sqrt N := by
  obtain ⟨K, hK, hT2⟩ := fp81s21_initial_T_L2 hδ hδh E hγ
  refine ⟨K, hK, fun N hN B hB u hu hub => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rw [← E.law_eq N]
    exact (E.static N hN).prob
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  let f : EucConfig p.d N → ℝ := fun X =>
    HRS.Whole.pair (HRS.Whole.empirical X) u - HRS.Whole.pair (r26t3_mu R 0) u
  have hfm : Measurable f := by
    dsimp [f]
    exact (S45.s45_measurable_pair_empirical (by omega) hu).sub measurable_const
  have hL2 := hT2 N hN B hB u hu hub
  have hfmem : MemLp f 2 (r26t3_Q R N) :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 (by simpa [f] using hL2.1)
  have hAbsMem : MemLp (fun X => |f X|) 2 (r26t3_Q R N) := hfmem.abs
  have hv := variance_nonneg (fun X => |f X|) (r26t3_Q R N)
  rw [variance_eq_sub hAbsMem] at hv
  simp only [Pi.pow_apply] at hv
  have hAbsNonneg : 0 ≤ ∫ X, |f X| ∂(r26t3_Q R N) :=
    integral_nonneg (fun X => abs_nonneg (f X))
  have hSq : (∫ X, |f X| ∂(r26t3_Q R N)) ^ 2 ≤
      ∫ X, f X ^ 2 ∂(r26t3_Q R N) := by
    have heq : ∫ X, (|f X|) ^ 2 ∂(r26t3_Q R N) =
        ∫ X, f X ^ 2 ∂(r26t3_Q R N) := by
      congr 1
      funext X
      rw [sq_abs]
    rw [← heq]
    linarith
  have hroot := Real.le_sqrt_of_sq_le hSq
  calc ∫ X, |f X| ∂(r26t3_Q R N)
      ≤ Real.sqrt (∫ X, f X ^ 2 ∂(r26t3_Q R N)) := hroot
    _ ≤ Real.sqrt ((K * B) ^ 2 / (N : ℝ)) := Real.sqrt_le_sqrt hL2.2
    _ = K * B / Real.sqrt N := by
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (mul_nonneg hK hB)]

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initial_T_L2
#print axioms HRS.Fp81.S21.fp81s21_initial_T_L1
