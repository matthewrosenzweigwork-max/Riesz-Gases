import HRS.MS.S82WP3
import HRS.MS.S82WK6

/-!
# S8.2 A05 (S82W), part 4: the centered pair statistic satisfies the envelope hypothesis of `gibbs_graph_closure`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section env
variable {d N : ℕ}

lemma w_tame_env {g : EucConfig d N → ℝ} (hg : u4Tame g) :
    ∃ A' M' : ℝ, 0 ≤ A' ∧ 0 ≤ M' ∧ ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → |g X| ≤ A' * u4Env M' M' X := by
  obtain ⟨C, p, q, hC, hp, hq, hb⟩ := hg
  have hK : 0 ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ) :=
    Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by norm_num
  refine ⟨C * ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ), max p q, mul_nonneg hC hK,
    le_trans hp (le_max_left _ _), fun X hX => ?_⟩
  refine (hb X hX).trans ?_
  have := u4Env_mono hp (le_max_left p q) hq (le_max_right p q) X hX
  calc C * u4Env p q X ≤ C * ((∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (2 : ℝ)) * u4Env (max p q) (max p q) X) :=
        mul_le_mul_of_nonneg_left this hC
    _ = _ := by ring

lemma u4Tame_onePlusNorm (p : ℝ) (hp : 0 ≤ p) : u4Tame (fun X : EucConfig d N => (1 + ‖X‖) ^ p) := by
  refine ⟨1, p, 0, zero_le_one, hp, le_rfl, fun X _ => ?_⟩
  unfold u4Env
  have h2 : 1 ≤ ∏ i, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-(0:ℝ))) := by
    refine u4_one_le_prod _ fun i => ?_
    have := Finset.prod_le_prod_of_subset_of_one_le₀ (f := fun j => 1 + ‖X i - X j‖ ^ (-(0:ℝ)))
      (s := ∅) (t := Finset.univ.erase i) (Finset.empty_subset _)
      (fun j _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(0:ℝ))])
      (fun j _ _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(0:ℝ))])
    simpa using this
  have h0 : 0 ≤ (1 + ‖X‖) ^ p := Real.rpow_nonneg (by linarith [norm_nonneg X]) _
  rw [abs_of_nonneg h0]
  nlinarith

lemma w_jb_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  refine Real.sqrt_le_iff.2 ⟨by linarith [norm_nonneg x], ?_⟩
  nlinarith [norm_nonneg x]

lemma w_wBq_le (hd : 2 ≤ d) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) {i j : Fin N} (hij : i ≠ j)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    wBq M A i j X ≤ A * (1 + ‖X‖) ^ (2 * M) * (2 + ‖X i - X j‖ ^ (-criticalS d)) := by
  have hr : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, hij, h⟩)
  have hs : 0 ≤ criticalS d := (u4_crit_pos hd).le
  have h1X : 0 ≤ 1 + ‖X‖ := by linarith [norm_nonneg X]
  have hpw : Phase2S82.pairWeight M (X i) (X j) ≤ (1 + ‖X‖) ^ (2 * M) := by
    unfold Phase2S82.pairWeight
    have a : ∀ k : Fin N, jbracket (X k) ^ M ≤ (1 + ‖X‖) ^ M := fun k =>
      Real.rpow_le_rpow (Real.sqrt_nonneg _) ((w_jb_le (X k)).trans (by linarith [norm_le_pi_norm X k])) hM
    calc jbracket (X i) ^ M * jbracket (X j) ^ M ≤ (1 + ‖X‖) ^ M * (1 + ‖X‖) ^ M :=
          mul_le_mul (a i) (a j) (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg h1X _)
      _ = (1 + ‖X‖) ^ (2 * M) := by
          rw [← Real.rpow_add (by linarith [norm_nonneg X])]; ring_nf
  have hsr : smallRadius (X i) (X j) ^ (-criticalS d) ≤ 1 + ‖X i - X j‖ ^ (-criticalS d) := by
    unfold smallRadius
    rcases le_total 1 ‖X i - X j‖ with h | h
    · rw [min_eq_left h, Real.one_rpow]
      linarith [Real.rpow_nonneg hr.le (-criticalS d)]
    · rw [min_eq_right h]; linarith
  unfold wBq
  have hw0 := w_pw_nonneg (d := d) M (X i) (X j)
  calc A * Phase2S82.pairWeight M (X i) (X j) * (1 + smallRadius (X i) (X j) ^ (-criticalS d))
      ≤ A * (1 + ‖X‖) ^ (2 * M) * (2 + ‖X i - X j‖ ^ (-criticalS d)) := by
        have hsr0 : 0 ≤ smallRadius (X i) (X j) ^ (-criticalS d) := by
          unfold smallRadius; exact Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) (by linarith) (by linarith) (by positivity)

lemma w_wBq_tame (hd : 2 ≤ d) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) :
    u4Tame (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X) := by
  refine u4Tame_sum _ _ fun i _ => u4Tame_sum _ _ fun j hj => ?_
  have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have ht : u4Tame (fun X : EucConfig d N => A * (1 + ‖X‖) ^ (2 * M) * (2 + ‖X i - X j‖ ^ (-criticalS d))) :=
    u4Tame_mul (u4Tame_const_mul A (u4Tame_onePlusNorm _ (by linarith)))
      (u4Tame_add (u4Tame_const 2) (u4Tame_pole hij (by linarith [u4_crit_pos hd])))
  refine u4Tame_of_le' ht fun X hX => ?_
  have h1 := w_wBq_le hd hM hA hij hX
  have h0 := wBq_nonneg M hA i j X
  have hr : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, hij, h⟩)
  have h2 : 0 ≤ A * (1 + ‖X‖) ^ (2 * M) * (2 + ‖X i - X j‖ ^ (-criticalS d)) :=
    mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by linarith [norm_nonneg X]) _))
      (by linarith [Real.rpow_nonneg hr.le (-criticalS d)])
  rw [abs_of_nonneg h0, abs_of_nonneg h2]; exact h1

theorem w_pairstat_env (hd : 2 ≤ d) {a beta : ℝ} {rho : Euc d → ℝ} {M A : ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hM : 0 ≤ M) (hQ : PairCorrector a beta rho M A f Q) (hA : 0 ≤ A) (c : ℝ) :
    ContDiffOn ℝ 2 (fun X : EucConfig d N => Phase2S82.pairStatistic Q X - c) (eucCollisionSet d N)ᶜ ∧
    ∃ A' M' : ℝ, 0 ≤ A' ∧ 0 ≤ M' ∧ ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |Phase2S82.pairStatistic Q X - c| + ‖fderiv ℝ (fun Y => Phase2S82.pairStatistic Q Y - c) X‖ +
        ‖iteratedFDeriv ℝ 2 (fun Y => Phase2S82.pairStatistic Q Y - c) X‖ ≤ A' * u4Env M' M' X := by
  obtain ⟨hF, hb⟩ := w_pairstat_jets (N := N) hd hQ hA c
  have ht : u4Tame (fun X : EucConfig d N => 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) *
      (∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X) + |c|) :=
    u4Tame_add (u4Tame_const_mul _ (w_wBq_tame hd hM hA)) (u4Tame_const _)
  obtain ⟨A', M', hA', hM', hAM⟩ := w_tame_env ht
  refine ⟨hF, A', M', hA', hM', fun X hX => ?_⟩
  refine (hb X hX).trans ?_
  exact (le_abs_self _).trans (hAM X hX)

end env

end HRS.MS.S82W
