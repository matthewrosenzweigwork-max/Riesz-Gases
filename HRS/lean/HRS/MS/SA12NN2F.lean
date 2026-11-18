import HRS.MS.SA12NN2E

/-!
# S.A.12 N2 (SA12N), part F: `hess_comm_finite` for `0 ≤ s < d - 1`

`|K(x-y)| |a(x) - a(y)| ≤ m ‖a‖_{C²} ‖x-y‖^{-(s+1)}` (an `L¹_loc` kernel since `s + 1 < d`), then `sa12n_young_pow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a HRS.MS.UniqN2b

variable {d : ℕ}

theorem sa12n_comm_lt (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∀ a : Euc d → ℝ, MemCb 2 a →
      ∀ (c : Euc d) (v : Euc d → ℝ), MemCb 2 v →
      Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (fun x =>
          a x * hessRiesz d s i j v x - hessRiesz d s i j (fun y => a y * v y) x)) 2 volume ≤
          ENNReal.ofReal (C * cbNorm 2 a * ρ ^ C₀) * eLpNorm v 2 volume := by
  have hsd : s < d := by linarith
  obtain ⟨C1, hC10, hC1⟩ := sa12n_young_pow hd (t := s + 1) (by linarith) (by linarith)
  set m : ℝ := max 1 s * (s + 3) with hm
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
    positivity
  refine ⟨m * C1 + 1, (d : ℝ), by positivity, Nat.cast_nonneg _, fun i j ρ hρ a ha c v hv hsupp c' r' hr' => ?_⟩
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  obtain ⟨hv2, hvc⟩ := sa12z3_memCb_cc hv hsupp
  have hA := sa12z3_cb_nonneg ha
  have hρ0 : 0 ≤ ρ := by linarith
  have hT : Continuous (fun x => a x * hessRiesz d s i j v x -
      hessRiesz d s i j (fun y => a y * v y) x) :=
    (ha2.continuous.mul (sa12n_hess_continuous hs0 hsd i j hv2 hvc)).sub
      (sa12n_hess_continuous hs0 hsd i j (ha2.mul hv2) hvc.mul_left)
  have key := hC1 (m * cbNorm 2 a) (by positivity) ρ hρ c v hv2.continuous.measurable hsupp c' r' hr'
    _ hT.aestronglyMeasurable (fun x _ => ?_)
  · refine key.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have : m * cbNorm 2 a * C1 * ρ ^ (d : ℝ) ≤ (m * C1 + 1) * cbNorm 2 a * ρ ^ (d : ℝ) := by
      have : 0 ≤ cbNorm 2 a * ρ ^ (d : ℝ) := by positivity
      nlinarith
    exact this
  · rw [sa12n_comm_pt_lt hd hs0 hs1 i j ha hv hvc x]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [k3_ae_ne hd x] with y hy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
    rw [← ofReal_norm, ← ofReal_norm (v y), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK := n0_qDH_bound hs0 i j hz
    have hl := sa12z3_a_lip ha x y
    have e : ‖x - y‖ ^ (-s - 2) * ‖x - y‖ = ‖x - y‖ ^ (-(s + 1)) := by
      rw [← Real.rpow_add_one hn.ne']; congr 1; ring
    have hpow : 0 ≤ ‖x - y‖ ^ (-s - 2) := by positivity
    calc ‖q09_DH s i (x - y) (EuclideanSpace.single j 1) * sa12n_wx a v x y‖
        = |q09_DH s i (x - y) (EuclideanSpace.single j 1)| * (|a x - a y| * |v y|) := by
          rw [Real.norm_eq_abs, abs_mul, sa12n_wx, ← sub_mul, abs_mul]
      _ ≤ (m * ‖x - y‖ ^ (-s - 2)) * ((cbNorm 2 a * ‖x - y‖) * |v y|) :=
          mul_le_mul hK (mul_le_mul_of_nonneg_right hl (abs_nonneg _)) (by positivity)
            (by positivity)
      _ = (m * cbNorm 2 a * ‖x - y‖ ^ (-(s + 1))) * ‖v y‖ := by
          rw [← e, Real.norm_eq_abs]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
