import HRS.Sections.Q17Aux5

/-!
# Q17 projection 3: strong convergence of `projPoly` on the path space (for `projection_strong`)

Uniform convergence of the spatial projections on compact sets (finite `ε`-nets, contractivity),
the pointwise interpolation estimate, and the strong limit `projPoly L w → w`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.Sec7

variable {d : ℕ}

/-- A path viewed as a continuous map on `[0,T]`. -/
def q17_wf {m T : ℝ} (w : PathSpace d m T) : C(Set.Icc (0 : ℝ) T, NegSobolev d m) := w

theorem q17_fourierProj_sub {m : ℝ} (L : ℕ) (x y : NegSobolev d m) :
    fourierProj m L (x - y) = fourierProj m L x - fourierProj m L y := by
  apply q17_ext
  intro k
  rw [q17_coord_fourierProj, q17_coord_sub, q17_coord_sub, q17_coord_fourierProj,
    q17_coord_fourierProj, mul_sub]

/-- Uniform strong convergence of the projections on compact sets. -/
theorem q17_unif_proj {m : ℝ} {K : Set (NegSobolev d m)} (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ x ∈ K, ‖fourierProj m L x - x‖ < ε := by
  obtain ⟨S, hSK, hSfin, hcover⟩ := finite_cover_balls_of_compact hK (e := ε / 3) (by positivity)
  have hev : ∀ᶠ L : ℕ in atTop, ∀ y ∈ S, ‖fourierProj m L y - y‖ < ε / 3 := by
    rw [Filter.eventually_all_finite hSfin]
    intro y _
    exact (tendsto_order.1 (q17_fourierProj_tendsto y)).2 (ε / 3) (by positivity)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hev
  refine ⟨L₀, fun L hL x hx => ?_⟩
  obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have hxy' : ‖x - y‖ < ε / 3 := mem_ball_iff_norm.1 hxy
  have hy := hL₀ L hL y hyS
  have hid : fourierProj m L x - x = fourierProj m L (x - y) + (fourierProj m L y - y) - (x - y) := by
    rw [q17_fourierProj_sub]
    abel
  rw [hid]
  have h1 := q17_norm_fourierProj_le L (x - y)
  calc ‖fourierProj m L (x - y) + (fourierProj m L y - y) - (x - y)‖
      ≤ ‖fourierProj m L (x - y) + (fourierProj m L y - y)‖ + ‖x - y‖ := norm_sub_le _ _
    _ ≤ ‖fourierProj m L (x - y)‖ + ‖fourierProj m L y - y‖ + ‖x - y‖ := by
        linarith [norm_add_le (fourierProj m L (x - y)) (fourierProj m L y - y)]
    _ < ε := by linarith

/-- One term of the interpolation: the projected value at a grid node `t_i = i T / 2^L` within
distance `< δ` of `t`. -/
theorem q17_term_bound {m T : ℝ} (hT : 0 < T) (L : ℕ) (w : PathSpace d m T) (ε₁ ε₂ δ : ℝ)
    (hL : T / (2 : ℝ) ^ L < δ)
    (hK1 : ∀ x ∈ Set.range (q17_wf w), ‖fourierProj m L x - x‖ < ε₁)
    (hK2 : ∀ p q : Set.Icc (0 : ℝ) T, dist p q < δ → ‖q17_wf w p - q17_wf w q‖ < ε₂)
    (t : Set.Icc (0 : ℝ) T) (i : ℕ) (hi : i ≤ 2 ^ L)
    (hsi : |(t : ℝ) * 2 ^ L / T - i| < 1) :
    ‖fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - q17_wf w t‖
      ≤ ε₁ + ε₂ := by
  have hi' : (i : ℝ) ≤ 2 ^ L := by exact_mod_cast hi
  have hp_mem : (i : ℝ) * T / 2 ^ L ∈ Set.Icc (0 : ℝ) T :=
    ⟨by positivity, by rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  have hproj : Set.projIcc 0 T hT.le ((i : ℝ) * T / 2 ^ L) =
      ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ := Set.projIcc_of_mem _ hp_mem
  rw [hproj]
  have hdist : dist (⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ : Set.Icc (0 : ℝ) T) t < δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have key : (i : ℝ) * T / 2 ^ L - (t : ℝ) =
        -((T / 2 ^ L) * ((t : ℝ) * 2 ^ L / T - i)) := by
      field_simp
      ring
    rw [key, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < T / 2 ^ L)]
    calc T / 2 ^ L * |(t : ℝ) * 2 ^ L / T - i| ≤ T / 2 ^ L * 1 :=
          mul_le_mul_of_nonneg_left hsi.le (by positivity)
      _ = T / 2 ^ L := mul_one _
      _ < δ := hL
  have h1 := hK2 _ t hdist
  have h2 := hK1 (q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) ⟨_, rfl⟩
  have hsplit : fourierProj m L (q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) - q17_wf w t =
      (fourierProj m L (q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) -
        q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) +
      (q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩ - q17_wf w t) := by
    abel
  show ‖fourierProj m L (q17_wf w ⟨(i : ℝ) * T / 2 ^ L, hp_mem⟩) - q17_wf w t‖ ≤ ε₁ + ε₂
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith)

/-- Pointwise estimate of the interpolated projection at a time `t ∈ [0,T]`. -/
theorem q17_proj_pointwise {m T : ℝ} (hT : 0 < T) (L : ℕ) (w : PathSpace d m T) (ε₁ ε₂ δ : ℝ)
    (hL : T / (2 : ℝ) ^ L < δ)
    (hK1 : ∀ x ∈ Set.range (q17_wf w), ‖fourierProj m L x - x‖ < ε₁)
    (hK2 : ∀ p q : Set.Icc (0 : ℝ) T, dist p q < δ → ‖q17_wf w p - q17_wf w q‖ < ε₂)
    (t : Set.Icc (0 : ℝ) T) :
    ‖(show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from projPoly m T hT.le L w) t - q17_wf w t‖
      ≤ ε₁ + ε₂ := by
  rw [q17_projPoly_apply]
  have hs0 : 0 ≤ (t : ℝ) * 2 ^ L / T := by
    have := t.2.1
    positivity
  have hsN : (t : ℝ) * 2 ^ L / T ≤ ((2 ^ L : ℕ) : ℝ) := by
    have := t.2.2
    rw [div_le_iff₀ hT]
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) L]
  have hsum := q17_hat_sum (2 ^ L) _ hs0 hsN
  have hsplit : ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
      fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - q17_wf w t =
      ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - q17_wf w t) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hsum, one_smul]
  rw [hsplit]
  calc ‖∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - q17_wf w t)‖
      ≤ ∑ i ∈ Finset.range (2 ^ L + 1), ‖q17_hat ((t : ℝ) * 2 ^ L / T) i •
        (fourierProj m L (PathSpace.at' w (Set.projIcc 0 T hT.le (i * T / 2 ^ L))) - q17_wf w t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i * (ε₁ + ε₂) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (q17_hat_nonneg _ _)]
        rcases eq_or_lt_of_le (q17_hat_nonneg ((t : ℝ) * 2 ^ L / T) i) with h0 | hpos
        · rw [← h0, zero_mul, zero_mul]
        · have hsi : |(t : ℝ) * 2 ^ L / T - i| < 1 := by
            by_contra hc
            push_neg at hc
            exact hpos.ne' (q17_hat_eq_zero hc)
          have hi' : i ≤ 2 ^ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          exact mul_le_mul_of_nonneg_left
            (q17_term_bound hT L w ε₁ ε₂ δ hL hK1 hK2 t i hi' hsi) hpos.le
    _ = (∑ i ∈ Finset.range (2 ^ L + 1), q17_hat ((t : ℝ) * 2 ^ L / T) i) * (ε₁ + ε₂) :=
        (Finset.sum_mul _ _ _).symm
    _ = ε₁ + ε₂ := by rw [hsum, one_mul]

end HRS.Sec7
