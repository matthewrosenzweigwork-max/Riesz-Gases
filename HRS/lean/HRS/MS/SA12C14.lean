import HRS.MS.SA12C13

/-!
# S.A.12(c), packet E7.03 (part 3): the tail integral and the volume of the centred cube

* `sa12c_tail_integrable`: `|z|^{-2(s+1)} 1_{|z| ≥ 4}` is integrable on `ℝ^d` when `d < 2(s+1)`.
* `sa12c_cube_volume`: `vol(centeredBox d L) ≤ V_d L^d`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_tail_integrable {s : ℝ} (hs0 : 0 ≤ s) (hs1 : (d : ℝ) < 2 * (s + 1)) :
    Integrable (fun z : Euc d => {z : Euc d | 4 ≤ ‖z‖}.indicator
      (fun z => (‖z‖ ^ (-(s + 1))) ^ 2) z) volume := by
  have hr : (Module.finrank ℝ (Euc d) : ℝ) < 2 * (s + 1) := by simpa using hs1
  have hint := (integrable_one_add_norm (E := Euc d) (μ := (volume : Measure (Euc d))) hr).const_mul ((5 / 4 : ℝ) ^ (2 * (s + 1)))
  refine Integrable.mono' hint ?_ (Eventually.of_forall fun z => ?_)
  · have hm : Measurable (fun z : Euc d => (‖z‖ ^ (-(s + 1))) ^ 2) :=
      (measurable_norm.pow_const _).pow_const 2
    exact (hm.indicator (isClosed_le continuous_const continuous_norm).measurableSet).aestronglyMeasurable
  · by_cases hz : 4 ≤ ‖z‖
    · rw [Set.indicator_of_mem (show z ∈ {z : Euc d | 4 ≤ ‖z‖} from hz), Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      have hz0 : 0 < ‖z‖ := by linarith
      have h1 : (‖z‖ ^ (-(s + 1))) ^ 2 = ‖z‖ ^ (-(2 * (s + 1))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
        congr 1; push_cast; ring
      have h2 : 1 + ‖z‖ ≤ (5 / 4) * ‖z‖ := by linarith
      have h3 : ((5 / 4) * ‖z‖) ^ (-(2 * (s + 1))) ≤ (1 + ‖z‖) ^ (-(2 * (s + 1))) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)
      rw [Real.mul_rpow (by norm_num) hz0.le] at h3
      have h4 : (5 / 4 : ℝ) ^ (2 * (s + 1)) * (5 / 4 : ℝ) ^ (-(2 * (s + 1))) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      rw [h1]
      show ‖z‖ ^ (-(2 * (s + 1))) ≤ (5 / 4 : ℝ) ^ (2 * (s + 1)) * (1 + ‖z‖) ^ (-(2 * (s + 1)))
      have h5 := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) (2 * (s + 1)))
      rw [← mul_assoc, h4, one_mul] at h5
      exact h5
    · rw [Set.indicator_of_notMem (show z ∉ {z : Euc d | 4 ≤ ‖z‖} from hz), norm_zero]
      positivity

/-- The closed cube `{z | ∀ i, |z i| ≤ L/2}` (contains both half-open centred cells). -/
def sa12cCube (d : ℕ) (L : ℝ) : Set (Euc d) := {z : Euc d | ∀ i, |z i| ≤ L / 2}

theorem sa12c_centered_sub_cube (L : ℝ) : centeredBox d L ⊆ sa12cCube d L :=
  fun z hz i => abs_le.2 ⟨(hz i).1, (hz i).2.le⟩

theorem sa12c_cube_meas (L : ℝ) : MeasurableSet (sa12cCube d L) := by
  have : sa12cCube d L = ⋂ i : Fin d, {z : Euc d | |z i| ≤ L / 2} := by
    ext z; simp [sa12cCube]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  exact measurableSet_le (by fun_prop) measurable_const

theorem sa12c_cube_subset (L : ℝ) (hL : 0 ≤ L) : sa12cCube d L ⊆ Metric.closedBall (0 : Euc d) (d * L) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hcoord : ∀ i, z i ^ 2 ≤ (L / 2) ^ 2 := by
    intro i
    have this := hz i
    exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
  have hsq : ‖z‖ ^ 2 ≤ ((d : ℝ) * L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin d, (L / 2) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = d * (L / 2) ^ 2 := by simp
      _ ≤ ((d : ℝ) * L) ^ 2 := by
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
          have hd1 : (d : ℝ) ≤ (d : ℝ) ^ 2 ∨ d = 0 := by
            rcases Nat.eq_zero_or_pos d with h | h
            · right; exact h
            · left; have : (1 : ℝ) ≤ d := by exact_mod_cast h
              nlinarith
          rcases hd1 with h | h
          · nlinarith [sq_nonneg L]
          · subst h; simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

theorem sa12c_cube_volume (L : ℝ) (hL : 0 ≤ L) :
    (volume (sa12cCube d L)).toReal ≤
      ((d : ℝ) ^ d * (volume (Metric.ball (0 : Euc d) 1)).toReal) * L ^ d := by
  have h1 := measure_mono (μ := (volume : Measure (Euc d))) (sa12c_cube_subset (d := d) L hL)
  rw [Measure.addHaar_closedBall _ _ (by positivity)] at h1
  have hfin : volume (Metric.ball (0 : Euc d) 1) < ⊤ := measure_ball_lt_top
  have h2 := ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  refine h2.trans (le_of_eq ?_)
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [mul_pow]; ring

end HRS.MH.AdjointRd.Phase2SA12C
