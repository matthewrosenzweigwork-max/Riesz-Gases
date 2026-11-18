import HRS.MS.S82UE1
import HRS.MS.S81G_Sing

/-!
# S8.2 A04 (S82U), part 1: the canonical Gibbs law at fixed `N`
Weight, Gaussian domination, probability, absolute continuity, null collision set.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82

section gibbs
variable {d N : ℕ}

/-- the unnormalised canonical weight -/
def u4w (d N : ℕ) (a beta : ℝ) (X : EucConfig d N) : ℝ :=
  Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X)

lemma u4_crit_pos (hd : 2 ≤ d) : 0 < criticalS d := by
  unfold criticalS
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma u4_pair_nonneg (hd : 2 ≤ d) (X : EucConfig d N) :
    0 ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), rieszKernel d (criticalS d) (X i - X j) := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hs : criticalS d ≠ 0 := (u4_crit_pos hd).ne'
  simp only [rieszKernel, hs, if_false]
  exact Real.rpow_nonneg (norm_nonneg _) _

lemma u4_H_ge (hd : 2 ≤ d) (a : ℝ) (X : EucConfig d N) :
    ∑ i, confinement a (X i) ≤
      HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X := by
  unfold HRS.Whole.canonicalHamiltonian
  have := u4_pair_nonneg hd X
  have h2 : 0 ≤ (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      rieszKernel d (criticalS d) (X i - X j) := mul_nonneg (by positivity) this
  linarith

lemma u4_w_le (hd : 2 ≤ d) {a beta : ℝ} (hbeta : 0 < beta) (X : EucConfig d N) :
    u4w d N a beta X ≤ ∏ i, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) := by
  unfold u4w
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  have := u4_H_ge hd a X
  have e : ∑ i, -(beta * a / 2) * ‖X i‖ ^ 2 = -beta * ∑ i, confinement a (X i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold confinement; ring
  rw [e]
  nlinarith

lemma u4_gauss_int1 (hd : 2 ≤ d) {c q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    Integrable (fun z : Euc d => (1 + ‖z‖) ^ q * Real.exp (-c * ‖z‖ ^ 2)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h0 := movtr_integrable_rpow_gauss (d := d) (by omega) (α := 0) (c := c) (by linarith) hc
  have h1 := movtr_integrable_rpow_gauss (d := d) (by omega) (α := q) (c := c) (by linarith) hc
  have hb := (h0.add h1).const_mul (2 ^ q)
  refine Integrable.mono' hb ?_ (Eventually.of_forall fun z => ?_)
  · exact (((measurable_const.add measurable_norm).pow_const q).mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_norm.pow_const 2)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)]
    have hz := norm_nonneg z
    have hk : (1 + ‖z‖) ^ q ≤ 2 ^ q * (1 + ‖z‖ ^ q) := by
      by_cases h1 : ‖z‖ ≤ 1
      · calc (1 + ‖z‖) ^ q ≤ 2 ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq
          _ ≤ 2 ^ q * (1 + ‖z‖ ^ q) := by
            have : 0 ≤ ‖z‖ ^ q := Real.rpow_nonneg hz _
            nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q]
      · push_neg at h1
        calc (1 + ‖z‖) ^ q ≤ (2 * ‖z‖) ^ q := Real.rpow_le_rpow (by positivity) (by linarith) hq
          _ = 2 ^ q * ‖z‖ ^ q := Real.mul_rpow (by norm_num) hz
          _ ≤ 2 ^ q * (1 + ‖z‖ ^ q) := by
            have : 0 ≤ ‖z‖ ^ q := Real.rpow_nonneg hz _
            nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q]
    have he := (Real.exp_pos (-c * ‖z‖ ^ 2)).le
    simp only [Real.rpow_zero]
    calc (1 + ‖z‖) ^ q * Real.exp (-c * ‖z‖ ^ 2) ≤ (2 ^ q * (1 + ‖z‖ ^ q)) * Real.exp (-c * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hk he
      _ = 2 ^ q * (1 * Real.exp (-c * ‖z‖ ^ 2) + ‖z‖ ^ q * Real.exp (-c * ‖z‖ ^ 2)) := by ring

end gibbs

end HRS.MS.S82U
