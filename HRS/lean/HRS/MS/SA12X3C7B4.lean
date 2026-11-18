import HRS.MS.SA12X3C7B3

/-!
# S.A.12 C7 (SA12X3), part B4: integral helpers (Cauchy-Schwarz, ball volume, smoothness of kernel convolutions)
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- Cauchy-Schwarz for continuous compactly supported functions. -/
theorem sa12x3_cs {f g : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) {A B : ℝ} (hA : ∫ x, f x ^ 2 ≤ A) (hB : ∫ x, g x ^ 2 ≤ B) :
    ∫ x, |f x| * |g x| ≤ Real.sqrt A * Real.sqrt B := by
  have hfi : Integrable (fun x => |f x| ^ 2) := by
    simp only [sq_abs]
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => f x ^ 2) (hf.pow 2)
      (hfc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hgi : Integrable (fun x => |g x| ^ 2) := by
    simp only [sq_abs]
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => g x ^ 2) (hg.pow 2)
      (hgc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hp2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hf.abs.aestronglyMeasurable).2 hfi
  have hq2 : MemLp (fun x => |g x|) (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hg.abs.aestronglyMeasurable).2 hgi
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => abs_nonneg (f x)) (Eventually.of_forall fun x => abs_nonneg (g x)) hp2 hq2
  simp only [Real.rpow_two, one_div] at h
  have e1 : ∫ x, |f x| ^ 2 = ∫ x, f x ^ 2 := by simp only [sq_abs]
  have e2 : ∫ x, |g x| ^ 2 = ∫ x, g x ^ 2 := by simp only [sq_abs]
  rw [e1, e2] at h
  have h1 : (∫ x, f x ^ 2) ^ (2⁻¹ : ℝ) ≤ Real.sqrt A := by
    calc (∫ x, f x ^ 2) ^ (2⁻¹ : ℝ) ≤ A ^ (2⁻¹ : ℝ) :=
          Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hA (by norm_num)
      _ = Real.sqrt A := by rw [Real.sqrt_eq_rpow, one_div]
  have h2 : (∫ x, g x ^ 2) ^ (2⁻¹ : ℝ) ≤ Real.sqrt B := by
    calc (∫ x, g x ^ 2) ^ (2⁻¹ : ℝ) ≤ B ^ (2⁻¹ : ℝ) :=
          Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hB (by norm_num)
      _ = Real.sqrt B := by rw [Real.sqrt_eq_rpow, one_div]
  refine h.trans (mul_le_mul h1 h2 (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)
    (Real.sqrt_nonneg _))

/-- A function between `0` and `1` vanishing outside a ball has integral at most the volume of the ball. -/
theorem sa12x3_int_le_vol {f : Euc d → ℝ} {c : Euc d} {ρ : ℝ} (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) (hs : ∀ x, x ∉ ball c ρ → f x = 0) :
    ∫ x, f x ≤ (volume (ball c ρ)).toReal := by
  have hb : IntegrableOn f (ball c ρ) volume :=
    (hf.continuousOn).integrableOn_compact (isCompact_closedBall c ρ) |>.mono_set ball_subset_closedBall
  have e : ∫ x, f x = ∫ x in ball c ρ, f x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hs x hx).symm
  rw [e]
  calc ∫ x in ball c ρ, f x ≤ ∫ x in ball c ρ, (1 : ℝ) :=
        setIntegral_mono_on hb (integrableOn_const (measure_ball_lt_top (x := c) (r := ρ)).ne)
          measurableSet_ball fun x _ => h1 x
    _ = (volume (ball c ρ)).toReal := by simp [Measure.real]

/-- Smoothness of a convolution of a continuous kernel with a smooth compactly supported function. -/
theorem sa12x3_conv_smooth {N : ℕ} {k g : Euc d → ℝ} (hk : LocallyIntegrable k (volume : Measure (Euc d))) (hg : ContDiff ℝ N g)
    (hgc : HasCompactSupport g) : ContDiff ℝ N (fun x => ∫ y, k (x - y) * g y) := by
  have hfun : (fun x => ∫ y, k (x - y) * g y) = k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g := by
    funext x'
    have h := integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun t => k t * g (x' - t)) x'
    simp only [sub_sub_cancel] at h
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← h]
  rw [hfun]
  exact hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hk hg

end HRS.MH.AdjointRd.Phase2SA12Near
