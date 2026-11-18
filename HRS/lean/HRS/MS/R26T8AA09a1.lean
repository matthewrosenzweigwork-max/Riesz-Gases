import HRS.MS.S82WP4
import HRS.MS.S82UA01
import HRS.MS.S82TB

/-!
# S8.2 observed-time layer, packet T8A.A09a1: tameness of pair and triple sums with pole-weighted kernels

If `|F x y| ≤ A ⟨x⟩^M ⟨y⟩^M pole(x,y)^k` off the diagonal then `X ↦ ∑_{i≠j} F (X i) (X j)` is dominated off collisions by a
constant times the polynomial pole envelope (`u4Tame`), hence lies in `L²(canonicalP)` when measurable; same for triple sums
with `triplePole`.  No pin or moment hypothesis is used.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W

variable {d N : ℕ}

theorem r26t8a_a09a1_pow_tame {g : EucConfig d N → ℝ} (hg : u4Tame g) (k : ℕ) :
    u4Tame (fun X => g X ^ k) := by
  induction k with
  | zero => simpa using (u4Tame_const (d := d) (N := N) 1)
  | succ k ih =>
    have := u4Tame_mul ih hg
    refine u4Tame_of_le' this fun X _ => ?_
    rw [pow_succ]

theorem r26t8a_a09a1_pole_nonneg (a b : Euc d) : 0 ≤ Phase2S82.pole a b := by
  unfold Phase2S82.pole smallRadius
  linarith [Real.rpow_nonneg (le_min zero_le_one (norm_nonneg (a - b))) (-criticalS d)]

theorem r26t8a_a09a1_pole_tame (hd : 2 ≤ d) {i j : Fin N} (hij : i ≠ j) :
    u4Tame (fun X : EucConfig d N => Phase2S82.pole (X i) (X j)) := by
  have ht : u4Tame (fun X : EucConfig d N => 2 + ‖X i - X j‖ ^ (-criticalS d)) :=
    u4Tame_add (u4Tame_const 2) (u4Tame_pole hij (by linarith [u4_crit_pos hd]))
  refine u4Tame_of_le' ht fun X hX => ?_
  have hr : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, hij, h⟩)
  have h0 : 0 ≤ ‖X i - X j‖ ^ (-criticalS d) := Real.rpow_nonneg hr.le _
  have hsr0 : 0 ≤ smallRadius (X i) (X j) ^ (-criticalS d) := by
    unfold smallRadius; exact Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
  have hsr : smallRadius (X i) (X j) ^ (-criticalS d) ≤ 1 + ‖X i - X j‖ ^ (-criticalS d) := by
    unfold smallRadius
    rcases le_total 1 ‖X i - X j‖ with h | h
    · rw [min_eq_left h, Real.one_rpow]; linarith
    · rw [min_eq_right h]; linarith
  unfold Phase2S82.pole
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

theorem r26t8a_a09a1_jb_tame {M : ℝ} (hM : 0 ≤ M) (k : Fin N) :
    u4Tame (fun X : EucConfig d N => jbracket (X k) ^ M) := by
  have ht := u4Tame_onePlusNorm (d := d) (N := N) M hM
  refine u4Tame_of_le' ht fun X _ => ?_
  have h1X : 0 ≤ 1 + ‖X‖ := by linarith [norm_nonneg X]
  have hj0 : 0 ≤ jbracket (X k) ^ M := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  rw [abs_of_nonneg hj0, abs_of_nonneg (Real.rpow_nonneg h1X _)]
  exact Real.rpow_le_rpow (Real.sqrt_nonneg _)
    ((HRS.MS.S82W.w_jb_le (X k)).trans (by linarith [norm_le_pi_norm X k])) hM

theorem r26t8a_a09a1_pairSum_tame (hd : 2 ≤ d) {F : Euc d → Euc d → ℝ} {M A : ℝ} (hM : 0 ≤ M)
    (hA : 0 ≤ A) (k : ℕ)
    (hb : ∀ x y, x ≠ y → |F x y| ≤ A * Phase2S82.pairWeight M x y * Phase2S82.pole x y ^ k) :
    u4Tame (fun X : EucConfig d N => Phase2S82.pairSum F X) := by
  unfold Phase2S82.pairSum
  refine u4Tame_sum _ _ fun i _ => u4Tame_sum _ _ fun j hj => ?_
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have ht : u4Tame (fun X : EucConfig d N =>
      A * (jbracket (X i) ^ M * jbracket (X j) ^ M) * Phase2S82.pole (X i) (X j) ^ k) :=
    u4Tame_mul (u4Tame_const_mul A (u4Tame_mul (r26t8a_a09a1_jb_tame hM i) (r26t8a_a09a1_jb_tame hM j)))
      (r26t8a_a09a1_pow_tame (r26t8a_a09a1_pole_tame hd hij) k)
  refine u4Tame_of_le' ht fun X hX => ?_
  have hXij : X i ≠ X j := fun h => hX ⟨i, j, hij, h⟩
  have h1 := hb (X i) (X j) hXij
  have h0 : 0 ≤ A * (jbracket (X i) ^ M * jbracket (X j) ^ M) * Phase2S82.pole (X i) (X j) ^ k :=
    mul_nonneg (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _))) (pow_nonneg (r26t8a_a09a1_pole_nonneg _ _) _)
  rw [abs_of_nonneg h0]
  exact h1

theorem r26t8a_a09a1_tripleSum_tame (hd : 2 ≤ d) {G : Euc d → Euc d → Euc d → ℝ} {M C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hb : ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
      |G x y z| ≤ C * jbracket x ^ M * jbracket y ^ M * jbracket z ^ M * Phase2S82.triplePole x y z) :
    u4Tame (fun X : EucConfig d N => Phase2S82.tripleSum G X) := by
  unfold Phase2S82.tripleSum
  refine u4Tame_sum _ _ fun i _ => u4Tame_sum _ _ fun j hj => u4Tame_sum _ _ fun k hk => ?_
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  have hP := r26t8a_a09a1_pole_tame (N := N) hd hij
  have hP2 := r26t8a_a09a1_pole_tame (N := N) hd hki.symm
  have hP3 := r26t8a_a09a1_pole_tame (N := N) hd hkj.symm
  have ht : u4Tame (fun X : EucConfig d N => C * jbracket (X i) ^ M * jbracket (X j) ^ M *
      jbracket (X k) ^ M * (Phase2S82.pole (X i) (X j) * Phase2S82.pole (X i) (X k) + Phase2S82.pole (X i) (X j) * Phase2S82.pole (X j) (X k) +
        Phase2S82.pole (X i) (X k) * Phase2S82.pole (X j) (X k))) := by
    refine u4Tame_mul ?_ (u4Tame_add (u4Tame_add (u4Tame_mul hP hP2) (u4Tame_mul hP hP3))
      (u4Tame_mul hP2 hP3))
    have := u4Tame_mul (u4Tame_mul (u4Tame_mul (u4Tame_const (d := d) (N := N) C)
      (r26t8a_a09a1_jb_tame hM i)) (r26t8a_a09a1_jb_tame hM j)) (r26t8a_a09a1_jb_tame hM k)
    exact this
  refine u4Tame_of_le' ht fun X hX => ?_
  have h1 := hb (X i) (X j) (X k) (fun h => hX ⟨i, j, hij, h⟩) (fun h => hX ⟨i, k, hki.symm, h⟩)
    (fun h => hX ⟨j, k, hkj.symm, h⟩)
  have hpp : ∀ a b : Euc d, 0 ≤ Phase2S82.pole a b := r26t8a_a09a1_pole_nonneg
  have h0 : 0 ≤ C * jbracket (X i) ^ M * jbracket (X j) ^ M * jbracket (X k) ^ M *
      (Phase2S82.pole (X i) (X j) * Phase2S82.pole (X i) (X k) + Phase2S82.pole (X i) (X j) * Phase2S82.pole (X j) (X k) +
        Phase2S82.pole (X i) (X k) * Phase2S82.pole (X j) (X k)) := by
    have hj : ∀ k : Fin N, 0 ≤ jbracket (X k) ^ M := fun k => Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have p1 := hpp (X i) (X j); have p2 := hpp (X i) (X k); have p3 := hpp (X j) (X k)
    have j1 := hj i; have j2 := hj j; have j3 := hj k
    positivity
  rw [abs_of_nonneg h0]
  exact h1

end HRS.MS.R26T8A
