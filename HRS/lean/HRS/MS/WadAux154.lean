import HRS.MS.WadAux153

/-!
# S8.3, packet S8G-5: approximation of a vanishing continuous `C_0`-valued section by separated sections

`s8g_sec_approx`: for a continuous `s : ℝ^d → C_0` with `‖s x'‖ → 0` and `ε > 0` there are finitely many `φ_i, b_i ∈ C_0` with
`‖s x' - Σ_i φ_i(x') b_i‖ ≤ ε` for all `x'` (partition of unity on a large ball subordinate to a fine cover).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_exists_radius {s : Euc d → S8gV d} (hdec : Tendsto (fun x => ‖s x‖) (cocompact (Euc d)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∃ ρ : ℝ, ∀ x', ρ < ‖x'‖ → ‖s x'‖ < ε := by
  have hev : ∀ᶠ x in cocompact (Euc d), ‖s x‖ < ε := hdec.eventually (gt_mem_nhds hε)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  refine ⟨ρ, fun x' hx' => hKs ?_⟩
  intro hxK
  have := hρ hxK
  rw [mem_closedBall_zero_iff] at this
  linarith

theorem s8g_sec_approx {s : Euc d → S8gV d} (hs : Continuous s)
    (hdec : Tendsto (fun x => ‖s x‖) (cocompact (Euc d)) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (φ b : ι → S8gV d), ∀ x', ‖s x' - ∑ i, φ i x' • b i‖ ≤ ε := by
  classical
  obtain ⟨ρ, hρ⟩ := s8g_exists_radius hdec (show 0 < ε / 3 by positivity)
  set K0 : Set (Euc d) := Metric.closedBall 0 (|ρ| + 1) with hK0
  set K1 : Set (Euc d) := Metric.closedBall 0 (|ρ| + 3) with hK1
  have hK1c : IsCompact K1 := isCompact_closedBall _ _
  have hK0c : IsCompact K0 := isCompact_closedBall _ _
  obtain ⟨δ0, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (hK1c.uniformContinuousOn_of_continuous hs.continuousOn) (ε / 3) (by positivity)
  set δ : ℝ := min δ0 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ0 one_pos
  obtain ⟨t, htK, htfin, hcov⟩ := finite_cover_balls_of_compact hK0c hδpos
  set t' : Finset (Euc d) := htfin.toFinset with ht'
  have hmem : ∀ i : t', (i : Euc d) ∈ K0 := fun i => htK (htfin.mem_toFinset.1 i.2)
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (ι := t') (X := Euc d) (isClosed_closedBall (x := (0 : Euc d)) (ε := |ρ| + 1))
    (fun i : t' => Metric.ball (i : Euc d) δ) (fun i => Metric.isOpen_ball) (by
      intro x hx
      have := hcov hx
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨y, hy, hxy⟩ := this
      exact ⟨⟨y, htfin.mem_toFinset.2 hy⟩, hxy⟩)
  have hsupp : ∀ (i : t') x', f i x' ≠ 0 → dist x' (i : Euc d) < δ := fun i x' hne =>
    hf i (subset_tsupport _ (Function.mem_support.2 hne))
  have hphi_tendsto : ∀ i : t', Tendsto (f i) (cocompact (Euc d)) (𝓝 0) := by
    intro i
    have hev : ∀ᶠ x in cocompact (Euc d), f i x = 0 := by
      have hc : IsCompact (Metric.closedBall (i : Euc d) δ) := isCompact_closedBall _ _
      filter_upwards [hc.compl_mem_cocompact] with x hx
      by_contra hne
      exact hx (Metric.mem_closedBall.2 (hsupp i x hne).le)
    exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)
  refine ⟨t', inferInstance, fun i => s8g_mk (f i) (f i).continuous (hphi_tendsto i), fun i => s (i : Euc d), ?_⟩
  intro x'
  have hsum_apply : ∀ x'' : Euc d, ∑ i : t', (s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x'' = ∑ i : t', f i x'' :=
    fun x'' => rfl
  have hone : ∑ i : t', f i x' ≤ 1 := by
    have := f.sum_le_one x'
    rwa [finsum_eq_sum_of_fintype] at this
  by_cases hx : x' ∈ K0
  · have hsum1 : ∑ i : t', f i x' = 1 := by
      have := f.sum_eq_one hx
      rwa [finsum_eq_sum_of_fintype] at this
    have e : s x' - ∑ i : t', (s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x' • s (i : Euc d) =
        ∑ i : t', f i x' • (s x' - s (i : Euc d)) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hsum1, one_smul]
      rfl
    rw [e]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : t', ‖f i x' • (s x' - s (i : Euc d))‖ ≤ ∑ i : t', f i x' * (ε / 3) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul, Real.norm_of_nonneg (f.nonneg i x')]
          by_cases hz : f i x' = 0
          · simp [hz]
          · refine mul_le_mul_of_nonneg_left ?_ (f.nonneg i x')
            have hd := hsupp i x' hz
            have hxK1 : x' ∈ K1 := by
              refine Metric.closedBall_subset_closedBall (by linarith) hx
            have hiK1 : (i : Euc d) ∈ K1 :=
              Metric.closedBall_subset_closedBall (by linarith) (hmem i)
            have := hδ x' hxK1 (i : Euc d) hiK1 (lt_of_lt_of_le hd (min_le_left _ _))
            rw [dist_eq_norm] at this
            exact this.le
      _ = (∑ i : t', f i x') * (ε / 3) := by rw [Finset.sum_mul]
      _ ≤ 1 * (ε / 3) := mul_le_mul_of_nonneg_right hone (by positivity)
      _ ≤ ε := by linarith
  · have hxn : |ρ| + 1 < ‖x'‖ := by
      rw [hK0, Metric.mem_closedBall, dist_zero_right] at hx
      exact not_le.1 hx
    have h1 : ‖s x'‖ < ε / 3 := hρ x' (by linarith [le_abs_self ρ])
    have h2 : ‖∑ i : t', (s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x' • s (i : Euc d)‖ ≤ ε / 3 := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i : t', ‖(s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x' • s (i : Euc d)‖
          ≤ ∑ i : t', f i x' * (ε / 3) := by
            refine Finset.sum_le_sum fun i _ => ?_
            show ‖f i x' • s (i : Euc d)‖ ≤ _
            rw [norm_smul, Real.norm_of_nonneg (f.nonneg i x')]
            by_cases hz : f i x' = 0
            · simp [hz]
            · refine mul_le_mul_of_nonneg_left ?_ (f.nonneg i x')
              have hd := hsupp i x' hz
              rw [dist_eq_norm] at hd
              have hi : ρ < ‖(i : Euc d)‖ := by
                have := norm_sub_norm_le x' (i : Euc d)
                have hd1 : ‖x' - (i : Euc d)‖ < 1 := lt_of_lt_of_le hd ((min_le_right _ _))
                linarith [le_abs_self ρ]
              exact (hρ _ hi).le
        _ = (∑ i : t', f i x') * (ε / 3) := by rw [Finset.sum_mul]
        _ ≤ 1 * (ε / 3) := mul_le_mul_of_nonneg_right hone (by positivity)
        _ = ε / 3 := one_mul _
    calc ‖s x' - ∑ i : t', (s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x' • s (i : Euc d)‖
        ≤ ‖s x'‖ + ‖∑ i : t', (s8g_mk (f i) (f i).continuous (hphi_tendsto i)) x' • s (i : Euc d)‖ :=
          norm_sub_le _ _
      _ ≤ ε := by linarith

end HRS.MS.Wad
