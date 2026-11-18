import HRS.MS.Fp81S21WeightedMoments7

/-! Transfer a negative-Sobolev moment bound to a measurable chart representative. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_coeff_aestronglyMeasurable
    {S : Type*} [MeasurableSpace S]
    (z : S → r26t6_Coeff) (hz : Measurable z) (P : Measure S) :
    AEStronglyMeasurable z P := by
  let ι : ∀ j : ℕ, ℝ →L[ℝ] r26t6_Coeff := fun j =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ℕ => ℝ) 2 j
  let sections : ℕ → S → r26t6_Coeff := fun n a =>
    ∑ j ∈ Finset.range n, ι j (z a j)
  have hcoord : ∀ j, AEStronglyMeasurable (fun a => z a j) P := by
    intro j
    have hMeas : Measurable (fun a => inner ℝ (z a)
        (lp.single 2 j (1 : ℝ))) :=
      (continuous_id.inner continuous_const).measurable.comp hz
    have hEq : (fun a => z a j) = fun a => inner ℝ (z a)
        (lp.single 2 j (1 : ℝ)) := by
      funext a
      simpa [lp.inner_single_right]
    rw [hEq]
    exact hMeas.aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := sections) ?_ ?_
  · intro n
    exact Finset.aestronglyMeasurable_fun_sum (Finset.range n) fun j _ =>
      (ι j).continuous.comp_aestronglyMeasurable (hcoord j)
  · filter_upwards [] with a
    exact coeffSection_tendsto (z a)

/-- The R2Wfm lower-integral estimate is for `r2NegSobNorm`; after the
pointwise W0 comparison and the exact `TestRep` norm identity, it bounds the
coefficient square. Measurability is used only to recover `MemLp` and the
ordinary integral; no measurability of `r2NegSobNorm` is assumed. -/
theorem fp81s21_rep_secondMoment
    {d r : ℕ} {Pw : ℝ} {S : Type*} [MeasurableSpace S]
    (E : r26t6_WeightedChart d r Pw) (P : Measure S)
    (T : S → (Euc d → ℝ) → ℝ) (z : S → r26t6_Coeff)
    (hz : Measurable z)
    (hrep : ∀ a, fp81s21_TestRep E (T a) (z a))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ a, dualNormE r Pw (T a) ≤
      ENNReal.ofReal C * r2NegSobNorm r Pw (T a))
    (hL : (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (2 : ℝ) ∂P) ≤
      ENNReal.ofReal D) :
    MemLp z 2 P ∧ (∫ a, ‖z a‖ ^ 2 ∂P) ≤ C ^ 2 * D := by
  have hpoint (a : S) :
      ENNReal.ofReal (‖z a‖ ^ 2) ≤
        ENNReal.ofReal (C ^ 2) * r2NegSobNorm r Pw (T a) ^ (2 : ℝ) := by
    have hn := (hrep a).2.2
    have hdual : ENNReal.ofReal ‖z a‖ ≤
        ENNReal.ofReal C * r2NegSobNorm r Pw (T a) := by
      rw [← hn]
      exact hb a
    have hsq : (ENNReal.ofReal ‖z a‖) ^ (2 : ℝ) ≤
        (ENNReal.ofReal C * r2NegSobNorm r Pw (T a)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hdual (by norm_num)
    have hleft : (ENNReal.ofReal ‖z a‖) ^ (2 : ℝ) =
        ENNReal.ofReal (‖z a‖ ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      congr 1
      exact Real.rpow_natCast _ _
    have hright :
        (ENNReal.ofReal C * r2NegSobNorm r Pw (T a)) ^ (2 : ℝ) =
          ENNReal.ofReal (C ^ 2) * r2NegSobNorm r Pw (T a) ^ (2 : ℝ) := by
      have hCpow : (ENNReal.ofReal C) ^ (2 : ℝ) = ENNReal.ofReal (C ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]
        exact congrArg ENNReal.ofReal (Real.rpow_natCast C 2)
      rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal C)
        (r2NegSobNorm r Pw (T a)) (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hCpow]
    rw [hleft, hright] at hsq
    exact hsq
  have hlin :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 2) ∂P) ≤
        ENNReal.ofReal (C ^ 2) * ENNReal.ofReal D := by
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (C ^ 2) *
          r2NegSobNorm r Pw (T a) ^ (2 : ℝ) ∂P := lintegral_mono hpoint
      _ = ENNReal.ofReal (C ^ 2) *
          (∫⁻ a, r2NegSobNorm r Pw (T a) ^ (2 : ℝ) ∂P) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal D :=
        mul_le_mul_right hL _
  have hzAEM : AEStronglyMeasurable z P :=
    fp81s21_coeff_aestronglyMeasurable z hz P
  have hnonneg : ∀ a, 0 ≤ ‖z a‖ ^ 2 := fun a => by positivity
  have hnormSqIntegrable : Integrable (fun a => ‖z a‖ ^ 2) P := by
    refine ⟨?_, ?_⟩
    · exact ((measurable_norm.comp hz).pow_const 2).aestronglyMeasurable
    · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
      have htop : ENNReal.ofReal (C ^ 2) * ENNReal.ofReal D < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt hlin htop
  have hmem : MemLp z 2 P := by
    rw [← integrable_norm_rpow_iff hzAEM (by norm_num) (by norm_num)]
    simpa [Real.rpow_natCast] using hnormSqIntegrable
  have hIntegralENN :
      (∫⁻ a, ENNReal.ofReal (‖z a‖ ^ 2) ∂P) =
        ENNReal.ofReal (∫ a, ‖z a‖ ^ 2 ∂P) := by
    exact (ofReal_integral_eq_lintegral_ofReal hnormSqIntegrable
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal :
      ENNReal.ofReal (∫ a, ‖z a‖ ^ 2 ∂P) ≤ ENNReal.ofReal (C ^ 2 * D) := by
    rw [hIntegralENN] at hlin
    calc
      _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal D := hlin
      _ = ENNReal.ofReal (C ^ 2 * D) := by
        rw [ENNReal.ofReal_mul (sq_nonneg C)]
  exact ⟨hmem, (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal⟩

#print axioms HRS.Fp81.S21.fp81s21_rep_secondMoment

end HRS.Fp81.S21
