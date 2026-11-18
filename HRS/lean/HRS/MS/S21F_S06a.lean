import HRS.MS.S21F_S05
import HRS.MS.WlStaticTie
import HRS.MS.WrStatic
import HRS.MS.QprepAux2

/-!
# S21F, packet R26-T3.S06 (part a): scalar variance and bias from the calibrated static bundle

`s21f_scalar_of_static`: from `evariance (HRS.Whole.linStat f) Q ≤ (C/N) ‖f‖²` and a marginal density `φ ∈ [0,C]` with `‖φ-1‖_{L²(μ)} ≤ C/N` get
`N Var(μ_N(f)) ≤ C ‖f‖²` and `|π_N(f) - μ(f)| ≤ C B/N` for `|f| ≤ B` (Cauchy-Schwarz through `Var(|u|) ≥ 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_bias {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {φ : Euc d → ℝ}
    (hφm : Measurable φ) (hφ0 : ∀ x, 0 ≤ φ x) {C : ℝ} (hφC : ∀ x, φ x ≤ C)
    (hφ2 : MemLp (fun x => φ x - 1) 2 μ) {r : ℝ} (hr : HRS.Whole.l2Norm μ (fun x => φ x - 1) ≤ r)
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |HRS.Whole.pair (μ.withDensity fun x => ENNReal.ofReal (φ x)) f - HRS.Whole.pair μ f| ≤ B * r := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hpair : HRS.Whole.pair (μ.withDensity fun x => ENNReal.ofReal (φ x)) f = ∫ x, φ x * f x ∂μ := by
    unfold HRS.Whole.pair
    rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (φ x)) (ENNReal.measurable_ofReal.comp hφm).aemeasurable
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hφ0 x)]
  have hφint : Integrable (fun x => φ x) μ := by
    refine (integrable_const C).mono' hφm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hφ0 x)]; exact hφC x
  have hfint : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hB x)
  have hφf : Integrable (fun x => φ x * f x) μ := by
    refine (hφint.norm.mul_const B).mono' (hφm.mul hf).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hB x) (norm_nonneg _)
  have hdiff : HRS.Whole.pair (μ.withDensity fun x => ENNReal.ofReal (φ x)) f - HRS.Whole.pair μ f =
      ∫ x, (φ x - 1) * f x ∂μ := by
    rw [hpair]; unfold HRS.Whole.pair
    rw [← integral_sub hφf hfint]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hdiff]
  have hu : Integrable (fun x => |φ x - 1|) μ :=
    (hφ2.integrable (by norm_num)).abs
  have hu2 : MemLp (fun x => |φ x - 1|) 2 μ := hφ2.abs
  have hjensen : (∫ x, |φ x - 1| ∂μ) ^ 2 ≤ ∫ x, (φ x - 1) ^ 2 ∂μ := by
    have h := variance_nonneg (fun x => |φ x - 1|) μ
    rw [variance_eq_sub hu2] at h
    simp only [Pi.pow_apply, sq_abs] at h
    linarith
  have hl2 : ∫ x, |φ x - 1| ∂μ ≤ r := by
    have h0 : 0 ≤ ∫ x, |φ x - 1| ∂μ := integral_nonneg fun x => abs_nonneg _
    have : (∫ x, |φ x - 1| ∂μ) ≤ Real.sqrt (∫ x, (φ x - 1) ^ 2 ∂μ) :=
      Real.le_sqrt_of_sq_le hjensen
    exact this.trans hr
  calc |∫ x, (φ x - 1) * f x ∂μ| ≤ ∫ x, |(φ x - 1) * f x| ∂μ := by
        simpa using abs_integral_le_integral_abs (μ := μ) (f := fun x => (φ x - 1) * f x)
    _ ≤ ∫ x, B * |φ x - 1| ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hu.const_mul B)
          (Eventually.of_forall fun x => ?_)
        show |(φ x - 1) * f x| ≤ B * |φ x - 1|
        rw [abs_mul]; nlinarith [hB x, abs_nonneg (φ x - 1), abs_nonneg (f x)]
    _ = B * ∫ x, |φ x - 1| ∂μ := integral_const_mul _ _
    _ ≤ B * r := mul_le_mul_of_nonneg_left hl2 hB0

theorem s21f_scalar_of_static {d N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Q : Measure (EucConfig d N)} {C : ℝ} (hN : 2 ≤ N) (hC : 0 ≤ C)
    (hlin : ∀ f : Euc d → ℝ, MemLp f 2 μ →
      evariance (HRS.Whole.linStat f) Q ≤ ENNReal.ofReal (C / N * ∫ x, f x ^ 2 ∂μ))
    (hmarg : ∃ φ : Euc d → ℝ, Measurable φ ∧
      HRS.Whole.firstMarginal Q = μ.withDensity (fun x => ENNReal.ofReal (φ x)) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ C) ∧
      MemLp (fun x => φ x - 1) 2 μ ∧ HRS.Whole.l2Norm μ (fun x => φ x - 1) ≤ C / N) :
    (∀ f : Euc d → ℝ, MemLp f 2 μ →
      (N : ℝ) * variance (fun X => HRS.Whole.pair (HRS.Whole.empirical X) f) Q ≤ C * ∫ x, f x ^ 2 ∂μ) ∧
    (∀ f : Euc d → ℝ, Measurable f → ∀ B : ℝ, (∀ x, |f x| ≤ B) →
      |HRS.Whole.pair (HRS.Whole.firstMarginal Q) f - HRS.Whole.pair μ f| ≤ C * B / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨fun f hf => ?_, fun f hf B hB => ?_⟩
  · have hI : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hv : variance (fun X => HRS.Whole.pair (HRS.Whole.empirical X) f) Q ≤ C / N * ∫ x, f x ^ 2 ∂μ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hlin f hf)
    calc (N : ℝ) * variance (fun X => HRS.Whole.pair (HRS.Whole.empirical X) f) Q ≤ N * (C / N * ∫ x, f x ^ 2 ∂μ) :=
          mul_le_mul_of_nonneg_left hv hN0.le
      _ = C * ∫ x, f x ^ 2 ∂μ := by field_simp
  · obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
    rw [hφeq]
    have := s21f_bias hφm (fun x => (hφb x).1) (fun x => (hφb x).2) hφ2 hφn hf hB
    calc _ ≤ B * (C / N) := this
      _ = C * B / N := by ring

end HRS.MS.R26T3
