import HRS.MS.SA12X2K

/-!
# S.A.12 N8 (SA12X2), part L: the `L²` bound of `[ω, T_i]` for a Lipschitz coefficient
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a HRS.MS.UniqN2b

variable {d : ℕ}

/-- The pointwise integral representation of the commutator. -/
theorem sa12x2_commT_pt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    {w v : Euc d → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hw : ContDiff ℝ 1 w)
    (hwL : ∀ x y, |w x - w y| ≤ L * ‖x - y‖) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (x : Euc d) :
    w x * firstRiesz d s i v x - firstRiesz d s i (fun y => w y * v y) x =
      ∫ y, q09_H s i (x - y) * ((w x - w y) * v y) := by
  have hwv : ContDiff ℝ 1 (fun y => w y * v y) := hw.mul hv
  have hwvc : HasCompactSupport (fun y => w y * v y) := hvc.mul_left
  have hlin := sa12x2_first_lin hs0 hsd i hv hvc hwv hwvc (w x) x
  obtain ⟨Bv, hBv⟩ := hv.continuous.bounded_above_of_compact_support hvc
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0)
  have hwx : ContDiff ℝ 1 (fun y => w x * v y - w y * v y) := (contDiff_const.mul hv).sub hwv
  have hwxc : HasCompactSupport (fun y => w x * v y - w y * v y) := hvc.mul_left.sub hwvc
  rw [← hlin]
  have hrep := sa12x2_first_repr hd hs0 hsd i hwx hwxc x (M := L * Bv) (by positivity) (fun y => by
    rw [Real.rpow_one, ← sub_mul, abs_mul]
    calc |w x - w y| * |v y| ≤ (L * ‖x - y‖) * Bv :=
          mul_le_mul (hwL x y) (by simpa [Real.norm_eq_abs] using hBv y) (abs_nonneg _) (by positivity)
      _ = L * Bv * ‖x - y‖ := by ring)
  rw [hrep]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- Real form of the commutator bound. -/
theorem sa12x2_commT_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (w v : Euc d → ℝ) (L : ℝ),
      0 ≤ L → ContDiff ℝ 1 w → (∀ x y, |w x - w y| ≤ L * ‖x - y‖) → ContDiff ℝ 1 v →
      HasCompactSupport v → Function.support v ⊆ closedBall c ρ →
      Real.sqrt (∫ x, ((closedBall c ρ).indicator (fun x => w x * firstRiesz d s i v x -
        firstRiesz d s i (fun y => w y * v y) x) x) ^ 2) ≤
        C * L * ρ ^ (d : ℝ) * Real.sqrt (∫ x, v x ^ 2) := by
  obtain ⟨C1, hC10, hC1⟩ := sa12n_young_pow hd (t := s) hs0 hsd
  refine ⟨max 1 s * C1, by positivity, fun i ρ hρ c w v L hL0 hw hwL hv hvc hsupp => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  have hcont : Continuous (fun x => w x * firstRiesz d s i v x -
      firstRiesz d s i (fun y => w y * v y) x) :=
    (hw.continuous.mul (sa12z3_firstRiesz_cont hs0 hsd i hv hvc)).sub
      (sa12z3_firstRiesz_cont hs0 hsd i (hw.mul hv) hvc.mul_left)
  have hm0 : 0 ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have key := hC1 (max 1 s * L) (by positivity) ρ hρ c v hv.continuous.measurable hsupp c ρ le_rfl
    _ hcont.aestronglyMeasurable (fun x _ => ?_)
  · refine sa12z3_l2_of_eLp (sa12z3_memLp_ind hcont c ρ)
      (hv.continuous.memLp_of_hasCompactSupport hvc) (by positivity) ?_
    refine key.trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) _
    ring
  · rw [sa12x2_commT_pt hd hs0 hsd i hL0 hw hwL hv hvc x]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [k3_ae_ne hd x] with y hy
    have hz : x - y ≠ 0 := sub_ne_zero.2 hy.symm
    have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
    rw [← ofReal_norm, ← ofReal_norm (v y), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hK : |q09_H s i (x - y)| ≤ max 1 s * ‖x - y‖ ^ (-s - 1) := n0_qH_bound hs0 i hz
    have hl := hwL x y
    have e : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
      rw [← Real.rpow_add_one hn.ne']; congr 1; ring
    have hpow : 0 ≤ ‖x - y‖ ^ (-s - 1) := by positivity
    calc ‖q09_H s i (x - y) * ((w x - w y) * v y)‖
        = |q09_H s i (x - y)| * (|w x - w y| * |v y|) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ (max 1 s * ‖x - y‖ ^ (-s - 1)) * ((L * ‖x - y‖) * |v y|) :=
          mul_le_mul hK (mul_le_mul_of_nonneg_right hl (abs_nonneg _)) (by positivity) (by positivity)
      _ = (max 1 s * L * ‖x - y‖ ^ (-s)) * ‖v y‖ := by
          rw [← e, Real.norm_eq_abs]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
