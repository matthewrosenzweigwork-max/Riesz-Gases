import HRS.Whole.Static
import Mathlib.Analysis.Calculus.ContDiff.Basic
import HRS.MS.R2PolyAux1
import HRS.Whole.MovtrAux2

noncomputable section
open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.S111K2
open HRS HRS.Whole
variable {d : ℕ}

/-- Jensen on `[0,1]`: `(∫ a)² ≤ ∫ a²` for continuous `a`. -/
lemma s111k2_sq_integral_le (a : ℝ → ℝ) (ha : Continuous a) :
    (∫ t in (0 : ℝ)..1, a t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, a t ^ 2 := by
  set m := ∫ t in (0 : ℝ)..1, a t with hm
  have h1 : IntervalIntegrable a MeasureTheory.volume 0 1 := ha.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => a t ^ 2) MeasureTheory.volume 0 1 :=
    (ha.pow 2).intervalIntegrable _ _
  have h3 : 0 ≤ ∫ t in (0 : ℝ)..1, (a t - m) ^ 2 := by
    refine intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have e : ∫ t in (0 : ℝ)..1, (a t - m) ^ 2 = (∫ t in (0 : ℝ)..1, a t ^ 2) - m ^ 2 := by
    have : ∀ t, (a t - m) ^ 2 = a t ^ 2 - (2 * m) * a t + m ^ 2 := fun t => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (h2.sub (h1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub h2 (h1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp [← hm]; ring
  linarith

/-- Integral Taylor estimate for a `C¹` vector field. -/
lemma s111k2_taylor_sq (v : Euc d → Euc d) (hv : ContDiff ℝ 1 v) (x y : Euc d) :
    ‖v x - v y‖ ^ 2 ≤ ‖x - y‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (y + t • (x - y))‖ ^ 2 := by
  set z := x - y with hz
  have hdiff : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hcont : Continuous fun t : ℝ => fderiv ℝ v (y + t • z) :=
    (hv.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => v (y + t • z)) (fderiv ℝ v (y + t • z) z) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => y + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add y
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt t h1
  have hint : IntervalIntegrable (fun t : ℝ => fderiv ℝ v (y + t • z) z) MeasureTheory.volume 0 1 :=
    (hcont.clm_apply continuous_const).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  have hxy : y + z = x := by simp [hz]
  simp only [one_smul, zero_smul, add_zero, hxy] at hFTC
  rw [← hFTC]
  set a : ℝ → ℝ := fun t => ‖fderiv ℝ v (y + t • z)‖ with ha
  have hac : Continuous a := hcont.norm
  have hn : ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (y + t • z) z‖ ≤ ‖z‖ * ∫ t in (0 : ℝ)..1, a t := by
    calc ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (y + t • z) z‖
        ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (y + t • z) z‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0 : ℝ)..1, ‖z‖ * a t := by
          refine intervalIntegral.integral_mono_on (by norm_num) (hint.norm) ?_ (fun t _ => ?_)
          · exact (hac.const_mul _).intervalIntegrable _ _
          · calc ‖fderiv ℝ v (y + t • z) z‖ ≤ ‖fderiv ℝ v (y + t • z)‖ * ‖z‖ :=
                ContinuousLinearMap.le_opNorm _ _
              _ = ‖z‖ * a t := by rw [ha]; ring
      _ = ‖z‖ * ∫ t in (0 : ℝ)..1, a t := intervalIntegral.integral_const_mul _ _
  calc ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (y + t • z) z‖ ^ 2
      ≤ (‖z‖ * ∫ t in (0 : ℝ)..1, a t) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = ‖z‖ ^ 2 * (∫ t in (0 : ℝ)..1, a t) ^ 2 := by ring
    _ ≤ ‖z‖ ^ 2 * ∫ t in (0 : ℝ)..1, a t ^ 2 :=
        mul_le_mul_of_nonneg_left (s111k2_sq_integral_le a hac) (sq_nonneg _)


lemma s111k2_grad_mul_norm {s : ℝ} (hs0 : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) :
    ‖z‖ * ‖rieszKernelGrad d s z‖ ≤ (s + 1) * (1 + rieszWeight s z) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hW : 0 ≤ rieszWeight s z := HRS.MS.Wr.wr3_rieszWeight_nonneg s z
  rw [HRS.Whole.movtr_rieszKernelGrad_norm s hs0 hz]
  have hpow : ‖z‖ * ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s) := by
    rw [mul_comm, ← Real.rpow_add_one hzpos.ne']
    congr 1; ring
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have : ‖z‖ * (movtr_sigma 0 * ‖z‖ ^ (-(0 : ℝ) - 1)) = 1 := by
      simp [movtr_sigma, Real.rpow_neg_one, hzpos.ne']
    rw [this]; nlinarith
  · have hw : rieszWeight s z = ‖z‖ ^ (-s) := by simp [rieszWeight, hpos.ne']
    have hσ : movtr_sigma s = s := by simp [movtr_sigma, hpos.ne']
    rw [hσ, ← mul_assoc, mul_comm ‖z‖ s, mul_assoc, hpow, ← hw]
    nlinarith


lemma s111k2_sq_grad_mul_norm {s : ℝ} (hs0 : 0 ≤ s) (z : Euc d) :
    ‖z‖ ^ 2 * ‖rieszKernelGrad d s z‖ ^ 2 ≤ ((s + 1) * (1 + rieszWeight s z)) ^ 2 := by
  by_cases hz : z = 0
  · subst hz
    have hW : 0 ≤ rieszWeight s (0 : Euc d) := HRS.MS.Wr.wr3_rieszWeight_nonneg s _
    simp; positivity
  · have := s111k2_grad_mul_norm hs0 hz
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) this 2

/-- Pointwise bound for finite partial sums of squared commutator kernels. -/
lemma s111k2_pointwise {s : ℝ} (hs0 : 0 ≤ s) (f : ℕ → Euc d → ℝ) (hf : ∀ j, ContDiff ℝ 2 (f j))
    {B Pw : ℝ} (hB : 0 ≤ B) (hPw : 0 ≤ Pw)
    (hsum : ∀ x, Summable (fun j => ‖fderiv ℝ (gradient (f j)) x‖ ^ 2) ∧
      (∑' j, ‖fderiv ℝ (gradient (f j)) x‖ ^ 2) ≤ B * (1 + ‖x‖) ^ (2 * Pw))
    (F : Finset ℕ) (x y : Euc d) :
    ∑ j ∈ F, (commutatorKernel d s (gradient (f j)) x y) ^ 2 ≤
      ((s + 1) * (1 + rieszWeight s (x - y))) ^ 2 *
        (B * ((1 + ‖x‖) ^ (2 * Pw) * (1 + ‖y‖) ^ (2 * Pw))) := by
  have hW : 0 ≤ rieszWeight s (x - y) := HRS.MS.Wr.wr3_rieszWeight_nonneg s _
  have hR : 0 ≤ ((s + 1) * (1 + rieszWeight s (x - y))) ^ 2 := sq_nonneg _
  have hP : 0 ≤ B * ((1 + ‖x‖) ^ (2 * Pw) * (1 + ‖y‖) ^ (2 * Pw)) := by positivity
  by_cases hxy : x = y
  · subst hxy
    simp only [commutatorKernel, sub_self, inner_zero_left, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  have hv : ∀ j, ContDiff ℝ 1 (gradient (f j)) := by
    intro j
    have h1 : ContDiff ℝ 1 (fderiv ℝ (f j)) := (hf j).fderiv_right (m := 1) (by norm_num)
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1
  set z := x - y with hz
  -- termwise Taylor
  have hterm : ∀ j, (commutatorKernel d s (gradient (f j)) x y) ^ 2 ≤
      ((s + 1) * (1 + rieszWeight s z)) ^ 2 *
        ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 := by
    intro j
    have h1 : (commutatorKernel d s (gradient (f j)) x y) ^ 2 ≤
        (‖gradient (f j) x - gradient (f j) y‖ * ‖rieszKernelGrad d s z‖) ^ 2 := by
      unfold commutatorKernel
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    have h2 := s111k2_taylor_sq (gradient (f j)) (hv j) x y
    have h3 := s111k2_sq_grad_mul_norm hs0 z
    calc (commutatorKernel d s (gradient (f j)) x y) ^ 2
        ≤ (‖gradient (f j) x - gradient (f j) y‖ * ‖rieszKernelGrad d s z‖) ^ 2 := h1
      _ = ‖gradient (f j) x - gradient (f j) y‖ ^ 2 * ‖rieszKernelGrad d s z‖ ^ 2 := by ring
      _ ≤ (‖z‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2) *
            ‖rieszKernelGrad d s z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = (‖z‖ ^ 2 * ‖rieszKernelGrad d s z‖ ^ 2) *
            ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 := by ring
      _ ≤ ((s + 1) * (1 + rieszWeight s z)) ^ 2 *
            ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (intervalIntegral.integral_nonneg (by norm_num)
            (fun t _ => sq_nonneg _))
  have hcont : ∀ j, Continuous fun t : ℝ => ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 := by
    intro j
    exact (((hv j).continuous_fderiv one_ne_zero).comp (by fun_prop)).norm.pow 2
  calc ∑ j ∈ F, (commutatorKernel d s (gradient (f j)) x y) ^ 2
      ≤ ∑ j ∈ F, ((s + 1) * (1 + rieszWeight s z)) ^ 2 *
          ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ((s + 1) * (1 + rieszWeight s z)) ^ 2 *
          ∫ t in (0 : ℝ)..1, ∑ j ∈ F, ‖fderiv ℝ (gradient (f j)) (y + t • z)‖ ^ 2 := by
        rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum]
        intro j _
        exact (hcont j).intervalIntegrable _ _
    _ ≤ ((s + 1) * (1 + rieszWeight s z)) ^ 2 *
          ∫ t in (0 : ℝ)..1, B * ((1 + ‖x‖) ^ (2 * Pw) * (1 + ‖y‖) ^ (2 * Pw)) := by
        refine mul_le_mul_of_nonneg_left ?_ hR
        refine intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_finset_sum F fun j _ => hcont j).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable _ _) (fun t ht => ?_)
        set ξ := y + t • z with hξ
        have h1 : ∑ j ∈ F, ‖fderiv ℝ (gradient (f j)) ξ‖ ^ 2 ≤ B * (1 + ‖ξ‖) ^ (2 * Pw) :=
          ((hsum ξ).1.sum_le_tsum F (fun j _ => sq_nonneg _)).trans (hsum ξ).2
        have h2 : ‖ξ‖ ≤ ‖x‖ + ‖y‖ := by
          have : ξ = (1 - t) • y + t • x := by
            rw [hξ, hz]; simp only [smul_sub, sub_smul, one_smul]; abel
          rw [this]
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
            Real.norm_of_nonneg ht.1]
          nlinarith [norm_nonneg x, norm_nonneg y, ht.1, ht.2]
        have h3 : (1 + ‖ξ‖) ^ (2 * Pw) ≤ (1 + ‖x‖) ^ (2 * Pw) * (1 + ‖y‖) ^ (2 * Pw) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          nlinarith [norm_nonneg x, norm_nonneg y]
        exact h1.trans (mul_le_mul_of_nonneg_left h3 hB)
    _ = _ := by
        rw [intervalIntegral.integral_const]; simp

end HRS.MS.S111K2
