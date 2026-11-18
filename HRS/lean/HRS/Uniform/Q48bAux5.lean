import HRS.Uniform.Q48bAux4

/-!
# Q48b, part 5: from the weighted bound at the level of `E_m` to the operator norm
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48b

open HRS HRS.PDE

variable {d : ℕ}

theorem q48b_wbound_mono {w : NonzeroLattice d → ℝ} {a : NonzeroLattice d → NonzeroLattice d → ℝ}
    {S T : Finset (NonzeroLattice d)} {α M M' : ℝ} (hM : 0 ≤ M) (hMM : M ≤ M')
    (h : WBound w a S T α M) (hw : ∀ i, 0 < w i) : WBound w a S T α M' := by
  intro z
  refine (h z).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · exact pow_le_pow_left₀ hM hMM 2
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (Real.rpow_nonneg (hw k).le _) (sq_nonneg _)

/-- The coordinates of `q48bFin m S (w^m x)` are those of `x` on `S`. -/
theorem q48bFin_coord (m : ℝ) (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ)
    (l : NonzeroLattice d) :
    NegSobolev.coord (q48bFin m S ζ) l = if l ∈ S then q48bW l ^ (-m) * ζ l else 0 := by
  classical
  unfold q48bFin
  rw [q48b_coord_sum]
  simp_rw [q48b_coord_smul, q48b_coord_basis]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hl h
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : l ≠ k := fun h => hl (h ▸ hk)
    simp [this]

theorem q48b_coord_eq_fourier {m : ℝ} (F : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.coord F l = q48bW l ^ (-m) * NegSobolev.fourierCoeff F l := by
  unfold NegSobolev.fourierCoeff
  have := q48b_rpow_neg_mul (q48bW_pos l) m
  simp only [q48bW] at this ⊢
  calc NegSobolev.coord F l = ((Lattice.jp l.1 ^ (-m)) * Lattice.jp l.1 ^ m) * NegSobolev.coord F l := by
        rw [this, one_mul]
    _ = _ := by ring

theorem q48b_norm_sq {m : ℝ} (F : NegSobolev d m) :
    ‖F‖ ^ 2 = ∑' l : NonzeroLattice d, NegSobolev.coord F l ^ 2 :=
  (NegSobolev.coord_sq F).2

theorem q48bFin_norm_sq (m : ℝ) (S : Finset (NonzeroLattice d)) (ζ : NonzeroLattice d → ℝ) :
    ‖q48bFin m S ζ‖ ^ 2 = ∑ k ∈ S, q48bW k ^ (-2 * m) * ζ k ^ 2 := by
  classical
  rw [q48b_norm_sq, tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [q48bFin_coord, if_pos hk, mul_pow, q48b_rpow_sq (q48bW_pos k)]
    congr 2; ring
  · intro k hk
    rw [q48bFin_coord, if_neg hk]; simp

/-- Operator norm bound from the weighted matrix bound at level `m`. -/
theorem q48b_opNorm_le {m : ℝ} (V : NegSobolev d m →L[ℝ] NegSobolev d m) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m V) S T m M) : ‖V‖ ≤ M := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound V hM fun x => ?_
  set ζ : NonzeroLattice d → ℝ := fun k => q48bW k ^ m * NegSobolev.coord x k with hζ
  -- finite truncations
  have hfin : ∀ S : Finset (NonzeroLattice d), ‖V (q48bFin m S ζ)‖ ≤ M * ‖q48bFin m S ζ‖ := by
    intro S
    have hsq : ‖V (q48bFin m S ζ)‖ ^ 2 ≤ (M * ‖q48bFin m S ζ‖) ^ 2 := by
      rw [q48b_norm_sq, mul_pow, q48bFin_norm_sq]
      refine Real.tsum_le_of_sum_le (fun l => sq_nonneg _) fun T => ?_
      have hT : ∀ l, NegSobolev.coord (V (q48bFin m S ζ)) l ^ 2 =
          q48bW l ^ (-2 * m) * (∑ k ∈ S, q48bMat m V l k * ζ k) ^ 2 := by
        intro l
        rw [q48b_coord_eq_fourier, q48bFin_V, mul_pow, q48b_rpow_sq (q48bW_pos l)]
        congr 2; ring
      simp_rw [hT]
      exact h S T ζ
    exact le_of_sq_le_sq hsq (by positivity) |>.trans le_rfl
  have hts : Tendsto (fun S : Finset (NonzeroLattice d) => q48bFin m S ζ) atTop (𝓝 x) := by
    have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num)
      (x : lp (fun _ : NonzeroLattice d => ℝ) 2)
    have heq : ∀ S : Finset (NonzeroLattice d), q48bFin m S ζ =
        ∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k) := by
      intro S
      refine lp.ext (funext fun l => ?_)
      have h1 : NegSobolev.coord (q48bFin m S ζ) l = if l ∈ S then NegSobolev.coord x l else 0 := by
        rw [q48bFin_coord]
        split_ifs
        · rw [hζ]
          simp only
          rw [← mul_assoc, q48b_rpow_neg_mul (q48bW_pos l) m, one_mul]
        · rfl
      have h2 : ((∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k) :
          lp (fun _ : NonzeroLattice d => ℝ) 2) : NonzeroLattice d → ℝ) l =
          if l ∈ S then NegSobolev.coord x l else 0 := by
        rw [lp.coeFn_sum, Finset.sum_apply]
        simp [lp.single_apply, Pi.single_apply]
      exact h1.trans h2.symm
    have hs' : Tendsto (fun S : Finset (NonzeroLattice d) =>
        ∑ k ∈ S, lp.single 2 k (NegSobolev.coord x k)) atTop
        (𝓝 (x : lp (fun _ : NonzeroLattice d => ℝ) 2)) := hs
    exact hs'.congr fun S => (heq S).symm
  have h1 : Tendsto (fun S : Finset (NonzeroLattice d) => ‖V (q48bFin m S ζ)‖) atTop (𝓝 ‖V x‖) :=
    (continuous_norm.tendsto _).comp ((V.continuous.tendsto x).comp hts)
  have h2 : Tendsto (fun S : Finset (NonzeroLattice d) => M * ‖q48bFin m S ζ‖) atTop (𝓝 (M * ‖x‖)) :=
    tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp hts)
  exact le_of_tendsto_of_tendsto' h1 h2 hfin

end HRS.Uniform.Q48b
