import HRS.MS.R26T8AP21i
import HRS.MS.R26T8AP02
import HRS.MS.R26T8AP01a

/-!
# S8.2 local Newton layer, packet T8A.P21 (part j): large-`z` jets of `Q`, kernel `k(z)` and its cutoff, existence of `chi`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_exists_cutoff (d : ℕ) : ∃ chi : Euc d → ℝ, NewtonCutoff chi := by
  let b : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun z => (b z + b (-z)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (b.contDiff.add (b.contDiff.comp contDiff_neg)).div_const 2
  · intro z; simp [add_comm]
  · intro z
    have h1 := b.nonneg' z
    have h2 := b.nonneg' (-z)
    have h3 := b.le_one (x := z)
    have h4 := b.le_one (x := -z)
    constructor <;> linarith
  · intro z hz
    have h1 : b z = 1 := b.one_of_mem_closedBall (by simpa using hz)
    have h2 : b (-z) = 1 := b.one_of_mem_closedBall (by simpa using hz)
    simp [h1, h2]
  · intro z hz
    have h1 : b z = 0 := b.zero_of_le_dist (by simpa using hz)
    have h2 : b (-z) = 0 := b.zero_of_le_dist (by simpa using hz)
    simp [h1, h2]

theorem r26t8a_nest_Q_large {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {A : ℝ}
    (hA : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) X z‖ ≤
      3 * A * ((q : ℝ) + 1) ^ 2 * (1 + ‖z‖) ^ 2 := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 le_rfl (by omega) 0)
  set L : ℝ →L[ℝ] ℝ := (-1 : ℝ) • ContinuousLinearMap.id ℝ ℝ with hL
  have hLn : ‖L‖ ≤ 1 := by
    refine (norm_smul _ _).trans_le ?_
    simpa using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)
  have u1h := r26t8a_u_joint_contDiff hf 1 (1 / 2) (p + q)
  have u1m := r26t8a_u_joint_contDiff hf 1 (-1 / 2) (p + q)
  have u20 := r26t8a_u_joint_contDiff hf 2 0 (p + q)
  have hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d =>
      r26t8a_u f Yw.1 Yw.2 (0 + 1) (1 / 2) + L (r26t8a_u f Yw.1 Yw.2 (0 + 1) (-1 / 2))) :=
    u1h.add (L.contDiff.comp u1m)
  have hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => L (r26t8a_u f Yw.1 Yw.2 (0 + 2) 0)) :=
    L.contDiff.comp u20
  have hQ : (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) = fun Yw =>
      (r26t8a_u f Yw.1 Yw.2 (0 + 1) (1 / 2) + L (r26t8a_u f Yw.1 Yw.2 (0 + 1) (-1 / 2))) +
        L (r26t8a_u f Yw.1 Yw.2 (0 + 2) 0) := by
    funext Yw
    rw [r26t8a_Q_eq_u]
    simp [hL]
    ring
  rw [hQ, r26t8a_nest_add p q z X hΦ hΨ]
  refine (norm_add_le _ _).trans ?_
  have hLu : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => L (r26t8a_u f Yw.1 Yw.2 (0 + 1) (-1 / 2))) := L.contDiff.comp u1m
  rw [r26t8a_nest_add p q z X u1h hLu]
  have b1 := r26t8a_nest_u_large hf hA 1 le_rfl (by norm_num) (1 / 2) (by norm_num [abs_of_pos]) p q hpq X z
  have b2 := r26t8a_nest_u_large hf hA 1 le_rfl (by norm_num) (-1 / 2) (by norm_num [abs_of_neg]) p q hpq X z
  have b3 := r26t8a_nest_u_large hf hA 2 (by norm_num) (by norm_num) 0 (by norm_num) p q hpq X z
  have c2 := r26t8a_nest_clm L hLn p q _ X z u1m
  have c3 := r26t8a_nest_clm L hLn p q _ X z u20
  have hq1 : (q : ℝ) + 1 ≤ ((q : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hz1 : 1 + ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  have e1 : A * ((q : ℝ) + 1) ^ 1 * (1 + ‖z‖) ^ 1 ≤ A * ((q : ℝ) + 1) ^ 2 * (1 + ‖z‖) ^ 2 := by
    rw [pow_one, pow_one]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hq1 hA0) hz1 (by positivity) (by positivity)
  have n1 := norm_add_le (r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_u f Yw.1 Yw.2 (0 + 1) (1 / 2)) X z)
    (r26t8a_nest p q (fun Yw : Euc d × Euc d => L (r26t8a_u f Yw.1 Yw.2 (0 + 1) (-1 / 2))) X z)
  linarith

end HRS.MS.R26T8A
