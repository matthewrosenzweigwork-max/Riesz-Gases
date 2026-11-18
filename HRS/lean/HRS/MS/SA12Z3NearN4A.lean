import HRS.MS.SA12Z2NearN3
import HRS.MS.SA12Z3NearN1

/-!
# S.A.12 N4 (SA12Z3), part A: the global commutator kernel and its Young bound

`κ(z) = min(|z|,2)|z|^{-s-1}` is integrable on `ℝ^d` for `d - 1 < s < d`; the bilinear Young inequality
`∬ |f(x)||h(y)| κ(x-y) ≤ (∫κ) (∫f² + ∫h²)/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The commutator kernel profile. -/
def sa12z3_kap (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := min ‖z‖ 2 * ‖z‖ ^ (-s - 1)

theorem sa12z3_kap_nonneg (s : ℝ) (z : Euc d) : 0 ≤ sa12z3_kap d s z := by
  unfold sa12z3_kap
  exact mul_nonneg (le_min (norm_nonneg _) (by norm_num)) (Real.rpow_nonneg (norm_nonneg _) _)

theorem sa12z3_kap_even (s : ℝ) (z : Euc d) : sa12z3_kap d s (-z) = sa12z3_kap d s z := by
  simp [sa12z3_kap]

theorem sa12z3_kap_measurable (s : ℝ) : Measurable (sa12z3_kap d s) := by
  unfold sa12z3_kap
  exact (continuous_norm.min continuous_const).measurable.mul (measurable_norm.pow_const _)

theorem sa12z3_kap_le (s : ℝ) (hs0 : 0 ≤ s) (z : Euc d) :
    sa12z3_kap d s z ≤ sa12z2_k d s (1 / 2) z + 2 ^ (s + 2) * (1 + ‖z‖) ^ (-(s + 1)) := by
  have hfar : 0 ≤ 2 ^ (s + 2) * (1 + ‖z‖) ^ (-(s + 1)) := by positivity
  have hk0 := sa12z2_k_nonneg (d := d) s (1 / 2) z
  by_cases hz : z = 0
  · subst hz
    have : sa12z3_kap d s (0 : Euc d) = 0 := by simp [sa12z3_kap]
    rw [this]; linarith
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases h1 : ‖z‖ ≤ 1
  · have hmin : min ‖z‖ 2 = ‖z‖ := min_eq_left (by linarith)
    have hmem : z ∈ Metric.closedBall (0 : Euc d) (2 * (1 / 2)) := by
      rw [mem_closedBall_zero_iff]; linarith
    have hk : sa12z2_k d s (1 / 2) z = ‖z‖ ^ (-s) := by
      unfold sa12z2_k; rw [Set.indicator_of_mem hmem]
    have : sa12z3_kap d s z = ‖z‖ ^ (-s) := by
      unfold sa12z3_kap
      rw [hmin, mul_comm, ← Real.rpow_add_one hpos.ne']
      congr 1; ring
    rw [this, hk]; linarith
  · push_neg at h1
    have hnm : z ∉ Metric.closedBall (0 : Euc d) (2 * (1 / 2)) := by
      rw [mem_closedBall_zero_iff]; linarith
    have hk : sa12z2_k d s (1 / 2) z = 0 := by
      unfold sa12z2_k; rw [Set.indicator_of_notMem hnm]
    rw [hk, zero_add]
    have hmin : min ‖z‖ 2 ≤ 2 := min_le_right _ _
    have h2 : ‖z‖ ^ (-s - 1) ≤ 2 ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1)) := by
      have h3 : (2 * ‖z‖) ^ (-(s + 1)) ≤ (1 + ‖z‖) ^ (-(s + 1)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      rw [Real.mul_rpow (by norm_num) hpos.le] at h3
      have h4 : (2 : ℝ) ^ (-(s + 1)) * ‖z‖ ^ (-(s + 1)) ≤ (1 + ‖z‖) ^ (-(s + 1)) := h3
      have h5 : (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-(s + 1)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h6 : ‖z‖ ^ (-s - 1) = 2 ^ (s + 1) * ((2 : ℝ) ^ (-(s + 1)) * ‖z‖ ^ (-(s + 1))) := by
        rw [← mul_assoc, h5, one_mul]; congr 1; ring
      rw [h6]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    calc sa12z3_kap d s z ≤ 2 * ‖z‖ ^ (-s - 1) :=
          mul_le_mul_of_nonneg_right hmin (Real.rpow_nonneg hpos.le _)
      _ ≤ 2 * (2 ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1))) := by gcongr
      _ = 2 ^ (s + 2) * (1 + ‖z‖) ^ (-(s + 1)) := by
          have h22 : (2 : ℝ) ^ (s + 2) = 2 ^ (s + 1) * 2 := by
            rw [show s + 2 = (s + 1) + 1 by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
          rw [h22]; ring

theorem sa12z3_kap_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs1 : (d : ℝ) - 1 < s) : Integrable (sa12z3_kap d s) := by
  have hk := sa12z2_k_integrable hd hs0 hsd (1 / 2)
  have hfar : Integrable (fun z : Euc d => (1 + ‖z‖) ^ (-(s + 1))) volume :=
    integrable_one_add_norm (E := Euc d) (μ := volume) (r := s + 1) (by simp; linarith)
  refine Integrable.mono' (hk.add (hfar.const_mul (2 ^ (s + 2)))) (sa12z3_kap_measurable s).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sa12z3_kap_nonneg s z)]
  exact sa12z3_kap_le s hs0 z

/-- Bilinear Young inequality for `κ`. -/
theorem sa12z3_young2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    {f h : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Integrable (fun p : Euc d × Euc d => |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2))
      (volume.prod volume) ∧
    ∫ p : Euc d × Euc d, |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume) ≤
      (∫ z, sa12z3_kap d s z) * ((∫ x, f x ^ 2) + ∫ x, h x ^ 2) / 2 := by
  have hk := sa12z3_kap_integrable hd hs0 hsd hs1
  have hkm := sa12z3_kap_measurable (d := d) s
  have hf2 : Integrable (fun x => f x ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (f := fun x => f x ^ 2) (hf.pow 2) (hfc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hh2 : Integrable (fun x => h x ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (f := fun x => h x ^ 2) (hh.pow 2) (hhc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  have hF1 : Integrable (fun p : Euc d × Euc d => h p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2))
      (volume.prod volume) := by
    have := hh2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
    simpa using this
  have hF2 : Integrable (fun p : Euc d × Euc d => f p.1 ^ 2 * sa12z3_kap d s (p.1 - p.2))
      (volume.prod volume) := by
    have := hf2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
    have h2 := this.swap
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, ContinuousLinearMap.mul_apply']
    rw [← neg_sub p.1 p.2, sa12z3_kap_even]
  have hmeas : AEStronglyMeasurable
      (fun p : Euc d × Euc d => |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2)) (volume.prod volume) := by
    refine ((hf.comp continuous_fst).abs.mul (hh.comp continuous_snd).abs).aestronglyMeasurable.mul ?_
    exact (hkm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hdom : ∀ p : Euc d × Euc d, |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2) ≤
      (1 / 2) * (h p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2) + f p.1 ^ 2 * sa12z3_kap d s (p.1 - p.2)) := by
    intro p
    have hk0 := sa12z3_kap_nonneg (d := d) s (p.1 - p.2)
    have hAM : |f p.1| * |h p.2| ≤ (1 / 2) * (h p.2 ^ 2 + f p.1 ^ 2) := by
      have := two_mul_le_add_sq |f p.1| |h p.2|
      rw [sq_abs, sq_abs] at this
      linarith
    calc |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2)
        ≤ ((1 / 2) * (h p.2 ^ 2 + f p.1 ^ 2)) * sa12z3_kap d s (p.1 - p.2) :=
          mul_le_mul_of_nonneg_right hAM hk0
      _ = _ := by ring
  have hint : Integrable (fun p : Euc d × Euc d => |f p.1| * |h p.2| * sa12z3_kap d s (p.1 - p.2))
      (volume.prod volume) := by
    refine Integrable.mono' ((hF1.add hF2).const_mul (1 / 2)) hmeas (Eventually.of_forall fun p => ?_)
    have hk0 := sa12z3_kap_nonneg (d := d) s (p.1 - p.2)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hk0)]
    have := hdom p
    simp only [Pi.add_apply]
    linarith
  refine ⟨hint, ?_⟩
  have hI1 : ∫ p : Euc d × Euc d, h p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume) =
      (∫ z, sa12z3_kap d s z) * ∫ x, h x ^ 2 := by
    rw [integral_prod_symm _ hF1]
    have : ∀ y : Euc d, ∫ x, h y ^ 2 * sa12z3_kap d s (x - y) = h y ^ 2 * ∫ z, sa12z3_kap d s z := by
      intro y
      rw [integral_const_mul, integral_sub_right_eq_self (sa12z3_kap d s) y]
    simp_rw [this]
    rw [integral_mul_const, mul_comm]
  have hI2 : ∫ p : Euc d × Euc d, f p.1 ^ 2 * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume) =
      (∫ z, sa12z3_kap d s z) * ∫ x, f x ^ 2 := by
    have hswap := integral_prod_swap (fun p : Euc d × Euc d => f p.2 ^ 2 * sa12z3_kap d s (p.2 - p.1))
      (μ := volume) (ν := volume)
    have hI1' : ∫ p : Euc d × Euc d, f p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume) =
        (∫ z, sa12z3_kap d s z) * ∫ x, f x ^ 2 := by
      have hF1' : Integrable (fun p : Euc d × Euc d => f p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2))
          (volume.prod volume) := by
        have := hf2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk
        simpa using this
      rw [integral_prod_symm _ hF1']
      have : ∀ y : Euc d, ∫ x, f y ^ 2 * sa12z3_kap d s (x - y) = f y ^ 2 * ∫ z, sa12z3_kap d s z := by
        intro y
        rw [integral_const_mul, integral_sub_right_eq_self (sa12z3_kap d s) y]
      simp_rw [this]
      rw [integral_mul_const, mul_comm]
    rw [← hI1', ← integral_prod_swap (fun p : Euc d × Euc d => f p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2))]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub p.1 p.2, sa12z3_kap_even]
  calc _ ≤ ∫ p : Euc d × Euc d, (1 / 2) * (h p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2) +
        f p.1 ^ 2 * sa12z3_kap d s (p.1 - p.2)) ∂(volume.prod volume) :=
        integral_mono hint ((hF1.add hF2).const_mul (1 / 2)) hdom
    _ = (1 / 2) * ((∫ p : Euc d × Euc d, h p.2 ^ 2 * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume)) +
        ∫ p : Euc d × Euc d, f p.1 ^ 2 * sa12z3_kap d s (p.1 - p.2) ∂(volume.prod volume)) := by
        rw [integral_const_mul, integral_add hF1 hF2]
    _ = (∫ z, sa12z3_kap d s z) * ((∫ x, f x ^ 2) + ∫ x, h x ^ 2) / 2 := by
        rw [hI1, hI2]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
