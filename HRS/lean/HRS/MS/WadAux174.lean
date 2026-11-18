import HRS.MS.WadAux173

/-!
# S8.3, packet S8H-5: order-zero theory of `tensorU`

`s8h_gap`: slices `F(x',·)` of a continuous decaying pair kernel vary continuously in the weighted sup norm.  `s8h_sec0`: for such `F` with
`|F| ≤ N w` and `t ∈ [0,T]`, the sections `x' ↦ U_t(F x')(y)` lie in `C_M` with `|U_t(F x')(y)| ≤ K₀ N ⟨x'⟩^M⟨y⟩^M` and
`|tensorU U t F x y| ≤ K₀² N ⟨x⟩^M⟨y⟩^M`; `s8h_tensor_sub`: `tensorU` is additive.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h_tendsto_prodMk_right (x' : Euc d) :
    Tendsto (fun y : Euc d => (x', y)) (cocompact (Euc d)) (cocompact (Euc d × Euc d)) := by
  refine Filter.tendsto_def.2 fun s hs => ?_
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hs
  refine Filter.mem_cocompact.2 ⟨Prod.snd '' K, hK.image continuous_snd, fun y hy => hKs ?_⟩
  intro hyK
  exact hy ⟨_, hyK, rfl⟩

/-- Outside a ball in the first variable the kernel is small relative to the weight. -/
theorem s8h_far {M : ℝ} {F : Euc d × Euc d → ℝ}
    (hdec : Tendsto (fun z => ‖F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, ∀ x' y' : Euc d, (ρ < ‖x'‖ ∨ ρ < ‖y'‖) → |F (x', y')| ≤ η * s8h_w M (x', y') := by
  have hev : ∀ᶠ z in cocompact (Euc d × Euc d), ‖F z‖ / s8h_w M z < η := hdec.eventually (gt_mem_nhds hη)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall (0 : Euc d × Euc d)
  refine ⟨ρ, fun x' y' h => ?_⟩
  have hzK : (x', y') ∉ K := by
    intro hz
    have := hρ hz
    rw [mem_closedBall_zero_iff, Prod.norm_def] at this
    rcases h with h | h
    · exact absurd (this.trans' (le_max_left _ _)) (not_le.2 h)
    · exact absurd (this.trans' (le_max_right _ _)) (not_le.2 h)
  have this : ‖F (x', y')‖ / s8h_w M (x', y') < η := hKs hzK
  have hp := s8h_w_pos M (x', y')
  rw [div_lt_iff₀ hp] at this
  rw [← Real.norm_eq_abs]
  exact this.le

theorem s8h_bound_of_pair {M : ℝ} {j : ℕ} {F : Euc d × Euc d → ℝ} (hF : S8hPair M j F) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ i ≤ j, ∀ z, ‖iteratedFDeriv ℝ i F z‖ ≤ N * s8h_w M z := by
  have hpi : ∀ i ≤ j, ∃ N : ℝ, 0 ≤ N ∧ ∀ z, ‖iteratedFDeriv ℝ i F z‖ ≤ N * s8h_w M z := by
    intro i hi
    have hev : ∀ᶠ z in cocompact (Euc d × Euc d), ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z < 1 :=
      (hF.2 i hi).eventually (gt_mem_nhds one_pos)
    obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
    have hcont : Continuous fun z => ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z :=
      ((hF.1.continuous_iteratedFDeriv (by exact_mod_cast hi)).norm).div (s8h_w_cont M)
        (fun z => (s8h_w_pos M z).ne')
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun z => ?_⟩
    have hp := s8h_w_pos M z
    rw [← div_le_iff₀ hp]
    by_cases hz : z ∈ K
    · have := hB z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hp.le)] at this
      exact this.trans (le_max_left _ _)
    · have h1 : ‖iteratedFDeriv ℝ i F z‖ / s8h_w M z < 1 := hKs hz
      exact h1.le.trans (le_max_right _ _)
  choose! N hN0 hN using hpi
  refine ⟨∑ i ∈ Finset.range (j + 1), N i, Finset.sum_nonneg fun i hi => hN0 i (by simpa [Nat.lt_succ_iff] using hi),
    fun i hi z => (hN i hi z).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (s8h_w_pos M z).le
  exact Finset.single_le_sum (f := N) (fun i hi => hN0 i (by simpa [Nat.lt_succ_iff] using hi))
    (Finset.mem_range.2 (by omega))

theorem s8h_gap {M : ℝ} (hM : 0 ≤ M) {F : Euc d × Euc d → ℝ} (hF : Continuous F)
    (hdec : Tendsto (fun z => ‖F z‖ / s8h_w M z) (cocompact (Euc d × Euc d)) (𝓝 0)) (x0 : Euc d) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x', ‖x' - x0‖ < δ → ∀ y, |F (x', y) - F (x0, y)| ≤ ε * jbracket y ^ M := by
  set Λ : ℝ := (3 * jbracket x0) ^ M with hΛ
  have hjx0 := s83_jb_pos x0
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (by linarith [s83_one_le_jb x0]) hM
  obtain ⟨ρ, hρ⟩ := s8h_far hdec (show 0 < ε / (2 * Λ) by positivity)
  have hS : IsCompact (Metric.closedBall x0 1 ×ˢ Metric.closedBall (0 : Euc d) ρ) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨δ', hδ', hδ⟩ := Metric.uniformContinuousOn_iff.1 (hS.uniformContinuousOn_of_continuous hF.continuousOn)
    ε hε
  refine ⟨min δ' 1, lt_min hδ' one_pos, fun x' hx' y => ?_⟩
  have hx1 : ‖x' - x0‖ < 1 := lt_of_lt_of_le hx' (min_le_right _ _)
  have hjy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have hjy0 : 0 ≤ jbracket y ^ M := by linarith
  have hjx' : jbracket x' ^ M ≤ Λ :=
    Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_three hx1) hM
  have hjx0' : jbracket x0 ^ M ≤ Λ :=
    Real.rpow_le_rpow (s83_jb_pos _).le (by linarith) hM
  by_cases hy : ρ < ‖y‖
  · have h1 := hρ x' y (Or.inr hy)
    have h2 := hρ x0 y (Or.inr hy)
    unfold s8h_w at h1 h2
    simp only at h1 h2
    have e1 : ε / (2 * Λ) * (jbracket x' ^ M * jbracket y ^ M) ≤ ε / (2 * Λ) * (Λ * jbracket y ^ M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjx' hjy0) (by positivity)
    have e2 : ε / (2 * Λ) * (jbracket x0 ^ M * jbracket y ^ M) ≤ ε / (2 * Λ) * (Λ * jbracket y ^ M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjx0' hjy0) (by positivity)
    have e3 : ε / (2 * Λ) * (Λ * jbracket y ^ M) * 2 = ε * jbracket y ^ M := by
      field_simp
    calc |F (x', y) - F (x0, y)| ≤ |F (x', y)| + |F (x0, y)| := abs_sub _ _
      _ ≤ ε / (2 * Λ) * (Λ * jbracket y ^ M) * 2 := by linarith
      _ = ε * jbracket y ^ M := e3
  · push Not at hy
    have := hδ (x', y) ⟨Metric.mem_closedBall.2 (by
        rw [dist_eq_norm]; exact hx1.le), Metric.mem_closedBall.2 (by rwa [dist_zero_right])⟩
      (x0, y) ⟨Metric.mem_closedBall_self zero_le_one, Metric.mem_closedBall.2 (by rwa [dist_zero_right])⟩
      (by
        rw [Prod.dist_eq]
        simp only [dist_self, max_lt_iff]
        exact ⟨by rw [dist_eq_norm]; exact lt_of_lt_of_le hx' (min_le_left _ _), hδ'⟩)
    rw [Real.dist_eq] at this
    calc |F (x', y) - F (x0, y)| ≤ ε := this.le
      _ = ε * 1 := (mul_one _).symm
      _ ≤ ε * jbracket y ^ M := mul_le_mul_of_nonneg_left hjy hε.le

end HRS.MS.Wad
