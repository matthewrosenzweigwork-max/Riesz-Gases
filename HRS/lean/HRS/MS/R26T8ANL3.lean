import HRS.MS.R26T8ANL2

/-!
# S8.2 T8A NL3: `r26t8a_nonlocal_pointwise`, the pointwise `nonlocal` field of `PairCorrector`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_nonlocal_pointwise (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (M : ℝ)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ G : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal 2 1 M (criticalS d - 2) A G →
      ∀ x y : Euc d, x ≠ y →
        |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y| ≤
          C * A * Phase2S82.pairWeight (M + 2) x y * (1 + smallRadius x y ^ (-criticalS d)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨C1, hC10, hP⟩ := r26t8a_p11_Px_same d hd 0 0 a beta M (criticalS d) ha hbeta hM hsd hchi
  set K : ℝ := max 2 (4 / (criticalS d) ^ 2) with hK
  have hK0 : 0 ≤ K := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨2 * C1 * (1 + K), by positivity, fun rho hrho G A hA hG x y hxy => ?_⟩
  have hG1 : Conormal (0 + 2) (0 + 1) M (criticalS d - 2) A G := hG
  have hGs : Conormal (0 + 2) (0 + 1) M (criticalS d - 2) A (fun x y => G y x) :=
    r26t8a_f24_conormal_swap hchi hG
  have P1 := hP rho hrho G A hA hG1
  have P2 := hP rho hrho (fun x y => G y x) A hA hGs
  have hsub : criticalS d - criticalS d = 0 := sub_self _
  have hr : 0 < min 1 ‖x - y‖ := lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  have hr1 : min 1 ‖x - y‖ ≤ 1 := min_le_left _ _
  have hrr : smallRadius x y = min 1 ‖x - y‖ := rfl
  have hw : 0 ≤ Phase2S82.pairWeight (M + 2) x y := by
    unfold Phase2S82.pairWeight jbracket
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hlog := r26t8a_nl_log_bound hs0 hr hr1
  -- the elementary bound `1 + (1+|log r|)^2 ≤ (1+K)(1 + r^{-s})`
  have hel : 1 + (1 + |Real.log (min 1 ‖x - y‖)|) ^ 2 ≤ (1 + K) * (1 + smallRadius x y ^ (-criticalS d)) := by
    have hp : 0 ≤ smallRadius x y ^ (-criticalS d) := Real.rpow_nonneg hr.le _
    rw [hrr] at hp ⊢
    nlinarith [hlog]
  have key : ∀ (F : Euc d → Euc d → ℝ), Conormal 0 2 (M + 2) (criticalS d - criticalS d) (C1 * A) F →
      ∀ u v : Euc d, u ≠ v → min 1 ‖u - v‖ = min 1 ‖x - y‖ →
        Phase2S82.pairWeight (M + 2) u v = Phase2S82.pairWeight (M + 2) x y →
        |F u v| ≤ C1 * A * Phase2S82.pairWeight (M + 2) x y * ((1 + K) * (1 + smallRadius x y ^ (-criticalS d))) := by
    intro F hF u v huv hmin hwt
    have h := r26t8a_nl_value hF u v huv
    rw [hsub] at h
    simp only [Nat.cast_zero, add_zero, neg_zero, Real.rpow_zero, one_mul] at h
    rw [hmin, hwt] at h
    refine h.trans ?_
    have hA1 : 0 ≤ C1 * A * Phase2S82.pairWeight (M + 2) x y := mul_nonneg (mul_nonneg hC10 hA) hw
    exact mul_le_mul_of_nonneg_left (hel) hA1
  have e1 := key _ P1 x y hxy rfl rfl
  have e2 := key _ P2 y x hxy.symm (by rw [norm_sub_rev]) (by unfold Phase2S82.pairWeight; ring)
  have hdecomp : pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y =
      (oneJ (critCoeff d a beta rho) (fun u => G u y) x -
        ∫ x', oneJ (critCoeff d a beta rho) (fun u => G u y) x' ∂(HRS.Whole.withDensityReal rho)) +
      (oneJ (critCoeff d a beta rho) (fun u => (fun x y => G y x) u x) y -
        ∫ x', oneJ (critCoeff d a beta rho) (fun u => (fun x y => G y x) u x) x' ∂(HRS.Whole.withDensityReal rho)) := by
    unfold pairJ HRS.Whole.projMean HRS.Whole.pair
    rfl
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  have := add_le_add e1 e2
  refine this.trans (le_of_eq ?_)
  ring

end HRS.MS.R26T8A

end
