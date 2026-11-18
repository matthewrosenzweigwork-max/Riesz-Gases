import HRS.Sections.Q17Aux4

/-!
# Q17 projection 2: the piecewise-linear projection `projPoly` as a contraction (for `projection_strong`)

Hat functions `q17_hat s i = max 0 (1 - |s - i|)` form a partition of unity on `[0, N]`; the
polygonal interpolation `projPoly` is linear and contractive in the sup norm of `PathSpace`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.Sec7

variable {d : ℕ}

/-- The hat function of the dyadic grid, evaluated at the grid coordinate `s`. -/
def q17_hat (s : ℝ) (i : ℕ) : ℝ := max 0 (1 - |s - i|)

theorem q17_hat_nonneg (s : ℝ) (i : ℕ) : 0 ≤ q17_hat s i := le_max_left _ _

theorem q17_hat_eq_zero {s : ℝ} {i : ℕ} (h : 1 ≤ |s - i|) : q17_hat s i = 0 :=
  max_eq_left (by linarith)

theorem q17_hat_sum : ∀ (N : ℕ) (s : ℝ), 0 ≤ s → s ≤ N →
    ∑ i ∈ Finset.range (N + 1), q17_hat s i = 1
  | 0, s, h0, hN => by
    have hs : s = 0 := le_antisymm (by exact_mod_cast hN) h0
    subst hs
    simp [q17_hat]
  | N + 1, s, h0, hN => by
    have hN' : s ≤ (N : ℝ) + 1 := by exact_mod_cast hN
    rw [Finset.sum_range_succ]
    by_cases hs : s ≤ N
    · have hIH := q17_hat_sum N s h0 hs
      have hz : q17_hat s (N + 1) = 0 := by
        apply q17_hat_eq_zero
        have hc : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [hc, abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      rw [hIH, hz, add_zero]
    · push_neg at hs
      rw [Finset.sum_range_succ]
      have hz : ∑ i ∈ Finset.range N, q17_hat s i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hi2 : i + 1 ≤ N := Finset.mem_range.1 hi
        have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi2
        apply q17_hat_eq_zero
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h1 : q17_hat s N = 1 - (s - N) := by
        unfold q17_hat
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - N)]
        rw [max_eq_right (by linarith)]
      have h2 : q17_hat s (N + 1) = s - N := by
        unfold q17_hat
        have habs : |s - ((N + 1 : ℕ) : ℝ)| = (N : ℝ) + 1 - s := by
          rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
          push_cast
          ring
        rw [habs, max_eq_right (by linarith)]
        ring
      rw [hz, h1, h2]
      ring

theorem q17_at_add {m T : ℝ} (w1 w2 : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (w1 + w2) t = PathSpace.at' w1 t + PathSpace.at' w2 t := rfl

theorem q17_at_smul {m T : ℝ} (c : ℝ) (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (c • w) t = c • PathSpace.at' w t := rfl

theorem q17_projPoly_apply {m T : ℝ} (hT : 0 ≤ T) (L : ℕ) (w : PathSpace d m T)
    (t : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w) t =
      ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT (i * T / 2 ^ L))) := rfl

theorem q17_pp_add_apply {m T : ℝ} (hT : 0 ≤ T) (L : ℕ) (w1 w2 : PathSpace d m T)
    (t : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w1 + projPoly m T hT L w2) t =
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w1) t +
        (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w2) t := rfl

theorem q17_pp_smul_apply {m T : ℝ} (hT : 0 ≤ T) (L : ℕ) (c : ℝ) (w : PathSpace d m T)
    (t : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from c • projPoly m T hT L w) t =
      c • (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT L w) t := rfl

theorem q17_projPoly_add {m T : ℝ} (hT : 0 < T) (L : ℕ) (w1 w2 : PathSpace d m T) :
    projPoly m T hT.le L (w1 + w2) = projPoly m T hT.le L w1 + projPoly m T hT.le L w2 := by
  show (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L (w1 + w2)) =
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w1 + projPoly m T hT.le L w2)
  apply ContinuousMap.ext
  intro t
  rw [q17_projPoly_apply, q17_pp_add_apply, q17_projPoly_apply, q17_projPoly_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [q17_at_add, q17_fourierProj_add, smul_add]

theorem q17_projPoly_smul {m T : ℝ} (hT : 0 < T) (L : ℕ) (c : ℝ) (w : PathSpace d m T) :
    projPoly m T hT.le L (c • w) = c • projPoly m T hT.le L w := by
  show (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L (c • w)) =
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from c • projPoly m T hT.le L w)
  apply ContinuousMap.ext
  intro t
  rw [q17_projPoly_apply, q17_pp_smul_apply, q17_projPoly_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [q17_at_smul, q17_fourierProj_smul, smul_comm]

/-- The projection `w ↦ projPoly L w` as a linear map on the path space. -/
def q17_projLin (m T : ℝ) (hT : 0 < T) (L : ℕ) : PathSpace d m T →ₗ[ℝ] PathSpace d m T where
  toFun w := projPoly m T hT.le L w
  map_add' w1 w2 := q17_projPoly_add hT L w1 w2
  map_smul' c w := by
    rw [RingHom.id_apply]
    exact q17_projPoly_smul hT L c w

theorem q17_projPoly_norm_le {m T : ℝ} (hT : 0 < T) (L : ℕ) (w : PathSpace d m T) :
    ‖projPoly m T hT.le L w‖ ≤ ‖w‖ := by
  have key : ∀ t : Set.Icc (0 : ℝ) T,
      ‖(show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w) t‖ ≤ ‖w‖ := by
    intro t
    rw [q17_projPoly_apply]
    have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
      have := t.2.1
      positivity
    have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
      have := t.2.2
      rw [div_le_iff₀ hT]
      push_cast
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
    calc ‖∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
          fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L)))‖
        ≤ ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
          fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * ‖w‖ := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (q17_hat_nonneg _ _)]
          refine mul_le_mul_of_nonneg_left ?_ (q17_hat_nonneg _ _)
          refine le_trans (q17_norm_fourierProj_le _ _) ?_
          exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) _
      _ = (∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i) * ‖w‖ :=
          (Finset.sum_mul _ _ _).symm
      _ = ‖w‖ := by
          rw [q17_hat_sum (2 ^ L) _ hs0 hsN, one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 key

end HRS.Sec7
