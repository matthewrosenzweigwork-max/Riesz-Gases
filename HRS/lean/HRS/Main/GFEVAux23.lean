import HRS.Main.GFEVAux22

/-!
# Packet GFEVG, part 23: the tail estimate and the quantity `N`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfev_coord_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl

theorem gfev_fc_sub {m : ℝ} (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (F - G) k = NegSobolev.fourierCoeff F k - NegSobolev.fourierCoeff G k := by
  unfold NegSobolev.fourierCoeff
  rw [gfev_coord_sub]; ring

theorem gfev_embed_trunc (γ n : ℕ) (w : NegSobolev d ((γ : ℝ) - 4)) :
    NegSobolev.embed (γ : ℝ) (q48bFin ((γ : ℝ) - 4) (gfevSn d n) (fun k => NegSobolev.fourierCoeff w k)) =
      (gfevP (gfevSn d n) (show L2 d from NegSobolev.embed (γ : ℝ) w) : NegSobolev d (γ : ℝ)) := by
  classical
  refine gfev_ext_fc fun k => ?_
  rw [gfev_fourierCoeff_embed (gfev_le4 γ), q48bFin_fourierCoeff]
  set Px : NegSobolev d (γ : ℝ) := (gfevP (gfevSn d n) (show L2 d from NegSobolev.embed (γ : ℝ) w) :
      NegSobolev d (γ : ℝ)) with hPx
  have hc : NegSobolev.coord Px k = if k ∈ gfevSn d n then NegSobolev.coord (NegSobolev.embed (γ : ℝ) w) k else 0 := by
    show (gfevP (gfevSn d n) (show L2 d from NegSobolev.embed (γ : ℝ) w)) k = _
    rw [gfevP_coord]; rfl
  show _ = NegSobolev.fourierCoeff Px k
  unfold NegSobolev.fourierCoeff
  rw [hc]
  by_cases hk : k ∈ gfevSn d n
  · rw [if_pos hk, if_pos hk, gfev_coord_embed (gfev_le4 γ)]
    unfold NegSobolev.fourierCoeff
    rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]; simp
  · rw [if_neg hk, if_neg hk]; simp

theorem gfev_tail_bound (γ n : ℕ) (w : NegSobolev d ((γ : ℝ) - 4)) :
    ‖NegSobolev.embed ((γ : ℝ) - 2)
        (w - q48bFin ((γ : ℝ) - 4) (gfevSn d n) (fun k => NegSobolev.fourierCoeff w k))‖ ≤
      (1 / ((n : ℝ) + 1)) ^ 2 * ‖w‖ := by
  classical
  set w' := w - q48bFin ((γ : ℝ) - 4) (gfevSn d n) (fun k => NegSobolev.fourierCoeff w k) with hw'
  set c : ℝ := (1 / ((n : ℝ) + 1)) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ k, |NegSobolev.coord (NegSobolev.embed ((γ : ℝ) - 2) w') k| ≤ c * |NegSobolev.coord w k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have e1 := gfev_coord_embed (gfev_le42 γ) w' k
    have e2 : NegSobolev.fourierCoeff w' k = NegSobolev.fourierCoeff w k -
        (if k ∈ gfevSn d n then NegSobolev.fourierCoeff w k else 0) := by
      rw [hw', gfev_fc_sub, q48bFin_fourierCoeff]
    by_cases hk : k ∈ gfevSn d n
    · rw [e1, e2, if_pos hk]; simp; positivity
    · rw [e1, e2, if_neg hk, sub_zero]
      have h4 := gfev_coord_eq_fc w k
      have hb : (n : ℝ) + 1 ≤ Lattice.jp k.1 := gfev_jp_ge (fun h => hk (mem_gfevSn.2 h))
      have h5 : Lattice.jp k.1 ^ (-((γ : ℝ) - 2)) = Lattice.jp k.1 ^ (-(2 : ℝ)) * Lattice.jp k.1 ^ (-((γ : ℝ) - 4)) := by
        rw [← Real.rpow_add hj]; congr 1; ring
      have h6 : Lattice.jp k.1 ^ (-(2 : ℝ)) ≤ c := by
        rw [hc, Real.rpow_neg hj.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div, inv_pow]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hb 2)
      rw [h5, mul_assoc, ← h4, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
      exact mul_le_mul_of_nonneg_right h6 (abs_nonneg _)
  obtain ⟨hs1, hn1⟩ := NegSobolev.coord_sq (NegSobolev.embed ((γ : ℝ) - 2) w')
  obtain ⟨hs2, hn2⟩ := NegSobolev.coord_sq w
  have hsq : ‖NegSobolev.embed ((γ : ℝ) - 2) w'‖ ^ 2 ≤ (c * ‖w‖) ^ 2 := by
    rw [hn1, mul_pow, hn2, ← tsum_mul_left]
    refine hs1.tsum_le_tsum (fun k => ?_) (hs2.mul_left _)
    have := hpt k
    calc NegSobolev.coord (NegSobolev.embed ((γ : ℝ) - 2) w') k ^ 2
        = |NegSobolev.coord (NegSobolev.embed ((γ : ℝ) - 2) w') k| ^ 2 := (sq_abs _).symm
      _ ≤ (c * |NegSobolev.coord w k|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = c ^ 2 * NegSobolev.coord w k ^ 2 := by rw [mul_pow, sq_abs]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _)) two_ne_zero).mp hsq

end HRS.GF
