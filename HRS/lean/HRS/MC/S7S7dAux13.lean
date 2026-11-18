import HRS.MC.S7S7dAux12

/-!
# Packet `s7_S7d_uniform_limits`, helper 13: uniform `L^1` tail of `W_N`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_W_tail (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ b : NonzeroLattice d → ℝ, Summable b ∧ (∀ k, 0 ≤ b k) ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ K : Finset (NonzeroLattice d),
        Measurable (fun X => min 2 ‖zetaE r (sed_Q d s N γ ρ) X - truncE K (zetaE r (sed_Q d s N γ ρ) X)‖) ∧
        ∫ X, min 2 ‖zetaE r (sed_Q d s N γ ρ) X - truncE K (zetaE r (sed_Q d s N γ ρ) X)‖
          ∂(sed_Q d s N γ ρ) ≤ (∑' k, b k) - ∑ k ∈ K, b k := by
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hr'' : (d : ℝ) < r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨c0, hc0, hW⟩ := HRS.MC.Sec7.S7c.s7c_Wk_L1 (r := r) hd hs0 hs hγ hρ
  have hb0 : ∀ k : NonzeroLattice d, 0 ≤ c0 * Lattice.jp k.1 ^ (-r) := fun k => by
    have := Torus.jp_pos k.1; positivity
  have hsum : Summable (fun k : NonzeroLattice d => c0 * Lattice.jp k.1 ^ (-r)) :=
    (HRS.MC.Sec7.S7c.s7c_summable_jp hr'').mul_left c0
  refine ⟨fun k => c0 * Lattice.jp k.1 ^ (-r), hsum, hb0, fun N hN K => ?_⟩
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  set Q := sed_Q d s N γ ρ with hQdef
  have hWm := HRS.MC.Sec7.S7c.s7c_zeta_meas hN hr' Q
  have hYm : ∀ k : NonzeroLattice d, Measurable (sed_Y Q (s7_phi r k)) := fun k =>
    HRS.MC.Sec7.S7c.s7c_sedY_meas hN Q
      (HRS.Q66.q66_cont_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r k))
  have hgm : Measurable (fun X => ‖zetaE r Q X - truncE K (zetaE r Q X)‖) :=
    (continuous_norm.comp (continuous_id.sub (s7d_truncE_continuous K))).measurable.comp hWm
  have hmm : Measurable (fun X => min 2 ‖zetaE r Q X - truncE K (zetaE r Q X)‖) :=
    measurable_const.min hgm
  refine ⟨hmm, ?_⟩
  set T : ℝ := (∑' k : NonzeroLattice d, c0 * Lattice.jp k.1 ^ (-r)) - ∑ k ∈ K, c0 * Lattice.jp k.1 ^ (-r) with hT
  have hT' : T = ∑' k : NonzeroLattice d, (if k ∈ K then 0 else c0 * Lattice.jp k.1 ^ (-r)) :=
    (s7d_tsum_indicator hsum K).symm
  have hT0 : 0 ≤ T := by
    rw [hT']
    exact tsum_nonneg fun k => by split_ifs <;> simp [hb0 k]
  have hsum2 : Summable (fun k : NonzeroLattice d => if k ∈ K then 0 else c0 * Lattice.jp k.1 ^ (-r)) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hb0 k])
      (fun k => by split_ifs <;> simp [hb0 k]) hsum
  have hlint : ∫⁻ X, ENNReal.ofReal ‖zetaE r Q X - truncE K (zetaE r Q X)‖ ∂Q ≤ ENNReal.ofReal T := by
    have hpt : ∀ X : Config d N, ENNReal.ofReal ‖zetaE r Q X - truncE K (zetaE r Q X)‖ ≤
        ∑' k : NonzeroLattice d, (if k ∈ K then 0 else ‖sed_Y Q (s7_phi r k) X‖ₑ) := by
      intro X
      rw [ofReal_norm_eq_enorm]
      refine (s7d_tail_enorm K (zetaE r Q X)).trans (le_of_eq ?_)
      refine tsum_congr fun k => ?_
      rw [HRS.MC.Sec7.S7c.s7c_coord_zeta hN hr' Q X k]
    calc _ ≤ ∫⁻ X, ∑' k : NonzeroLattice d, (if k ∈ K then 0 else ‖sed_Y Q (s7_phi r k) X‖ₑ) ∂Q :=
          lintegral_mono hpt
      _ = ∑' k : NonzeroLattice d, ∫⁻ X, (if k ∈ K then 0 else ‖sed_Y Q (s7_phi r k) X‖ₑ) ∂Q := by
          refine lintegral_tsum fun k => ?_
          by_cases hk : k ∈ K
          · simp [hk]
          · simp only [hk, if_false]; exact (hYm k).enorm.aemeasurable
      _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal
            (if k ∈ K then 0 else c0 * Lattice.jp k.1 ^ (-r)) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hk : k ∈ K
          · simp [hk]
          · simp only [hk, if_false]
            obtain ⟨hint, hb⟩ := hW N hN k
            rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
            exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hb)
      _ = ENNReal.ofReal T := by
          rw [hT']
          exact (ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> simp [hb0 k]) hsum2).symm
  have hmin : ∫⁻ X, ENNReal.ofReal (min 2 ‖zetaE r Q X - truncE K (zetaE r Q X)‖) ∂Q ≤ ENNReal.ofReal T :=
    (lintegral_mono fun X => ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hlint
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun X => le_min (by norm_num) (norm_nonneg _)) hmm.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal T).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmin
    _ = T := ENNReal.toReal_ofReal hT0

end HRS.MC.Sec7.S7d

end
