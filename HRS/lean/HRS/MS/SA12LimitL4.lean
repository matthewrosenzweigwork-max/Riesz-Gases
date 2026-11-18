import HRS.MS.SA12LimitDefs

/-!
# S.A.12 L4: weak sequential compactness of equi-Lipschitz bounded paths in a separable Hilbert space
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff BoundedContinuousFunction

namespace HRS.MH.AdjointRd.Phase2SA12Limit

section Aux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded sequence whose pairings with a dense family converge converges weakly. -/
theorem sa12x_weak_limit (e : ℕ → H) (he : DenseRange e) (B : ℝ) (hB : 0 ≤ B) (x : ℕ → H)
    (hx : ∀ k, ‖x k‖ ≤ B) (l : ℕ → ℝ)
    (hl : ∀ j, Tendsto (fun k => inner ℝ (x k) (e j)) atTop (𝓝 (l j))) :
    ∃ v : H, ‖v‖ ≤ B ∧ ∀ h : H, Tendsto (fun k => inner ℝ (x k) h) atTop (𝓝 (inner ℝ v h)) := by
  have hcau : ∀ h : H, CauchySeq (fun k => inner ℝ (x k) h) := by
    intro h
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨j, hj⟩ := he.exists_dist_lt h (show 0 < ε / (4 * (B + 1)) by positivity)
    have hc := (hl j).cauchySeq
    rw [Metric.cauchySeq_iff] at hc
    obtain ⟨N, hN⟩ := hc (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [Real.dist_eq] at h1 ⊢
    have h2 : inner ℝ (x m) h - inner ℝ (x n) h =
        (inner ℝ (x m) (e j) - inner ℝ (x n) (e j)) + inner ℝ (x m - x n) (h - e j) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have h3 : |inner ℝ (x m - x n) (h - e j)| ≤ 2 * B * (ε / (4 * (B + 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have : ‖x m - x n‖ ≤ 2 * B := by
        have := norm_sub_le (x m) (x n); linarith [hx m, hx n]
      have hn' : ‖h - e j‖ ≤ ε / (4 * (B + 1)) := by rw [← dist_eq_norm]; exact hj.le
      exact mul_le_mul this hn' (norm_nonneg _) (by linarith)
    rw [h2]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    have h4 : 2 * B * (ε / (4 * (B + 1))) ≤ ε / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 : |inner ℝ (x m) (e j) - inner ℝ (x n) (e j)| < ε / 2 := h1
    linarith
  choose w hw using fun h => cauchySeq_tendsto_of_complete (hcau h)
  have hwb : ∀ h, |w h| ≤ B * ‖h‖ := by
    intro h
    refine le_of_tendsto ((hw h).abs) (Filter.Eventually.of_forall fun k => ?_)
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hx k) (norm_nonneg _))
  let Λ : H →ₗ[ℝ] ℝ :=
    { toFun := w
      map_add' := fun h1 h2 => tendsto_nhds_unique (hw (h1 + h2))
        (by simpa [inner_add_right] using (hw h1).add (hw h2))
      map_smul' := fun c h => tendsto_nhds_unique (hw (c • h))
        (by simpa [inner_smul_right] using (hw h).const_mul c) }
  let Λc : H →L[ℝ] ℝ := LinearMap.mkContinuous Λ B (fun h => by
    rw [Real.norm_eq_abs]; exact hwb h)
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Λc, ?_, fun h => ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le Λ hB _
  · rw [InnerProductSpace.toDual_symm_apply]
    exact hw h

omit [CompleteSpace H] in
/-- Arzelà–Ascoli extraction: one subsequence along which every scalar pairing path converges uniformly. -/
theorem sa12x_extract (e : ℕ → H) (B T : ℝ) (u : ℕ → ℝ → H)
    (hu : ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, ‖u n τ‖ ≤ B)
    (hequi : ∀ j, ∃ K : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, ∀ σ ∈ Icc (0 : ℝ) T,
      |inner ℝ (u n τ - u n σ) (e j)| ≤ K * |τ - σ|) :
    ∃ (φ : ℕ → ℕ) (a : ℕ → Icc (0 : ℝ) T →ᵇ ℝ), StrictMono φ ∧
      ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ τ : Icc (0 : ℝ) T,
        |inner ℝ (u (φ k) τ) (e j) - a j τ| ≤ ε := by
  choose K hK using hequi
  have hKp0 : ∀ j, 0 ≤ max (K j) 0 := fun j => le_max_right _ _
  have hlip : ∀ j n (τ σ : Icc (0 : ℝ) T),
      |inner ℝ (u n τ) (e j) - inner ℝ (u n σ) (e j)| ≤ max (K j) 0 * |(τ : ℝ) - σ| := by
    intro j n τ σ
    have := hK j n τ τ.2 σ σ.2
    rw [inner_sub_left] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have hcont : ∀ j n, Continuous (fun τ : Icc (0 : ℝ) T => inner ℝ (u n τ) (e j)) := by
    intro j n
    refine (LipschitzWith.of_dist_le_mul (K := ⟨max (K j) 0, hKp0 j⟩) fun τ σ => ?_).continuous
    have := hlip j n τ σ
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
    exact this
  let F : ℕ → ℕ → (Icc (0 : ℝ) T →ᵇ ℝ) := fun n j =>
    BoundedContinuousFunction.mkOfCompact ⟨_, hcont j n⟩
  have hF : ∀ n j (τ : Icc (0 : ℝ) T), F n j τ = inner ℝ (u n τ) (e j) := fun _ _ _ => rfl
  have hbound : ∀ n j (τ : Icc (0 : ℝ) T), |F n j τ| ≤ B * ‖e j‖ := by
    intro n j τ
    rw [hF]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hu n τ τ.2) (norm_nonneg _))
  have hcompact : ∀ j, IsCompact (closure (Set.range fun n => F n j)) := by
    intro j
    refine BoundedContinuousFunction.arzela_ascoli (Icc (-(B * ‖e j‖)) (B * ‖e j‖)) isCompact_Icc _ ?_ ?_
    · rintro f x ⟨n, rfl⟩
      exact abs_le.1 (hbound n j x)
    · refine Metric.equicontinuous_of_continuity_modulus (fun x => max (K j) 0 * x) ?_ _ ?_
      · have : Tendsto (fun x : ℝ => max (K j) 0 * x) (𝓝 0) (𝓝 (max (K j) 0 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this
      · rintro x y ⟨_, ⟨n, rfl⟩⟩
        have := hlip j n x y
        simpa [Real.dist_eq, Subtype.dist_eq, hF] using this
  have hcomp : IsCompact (Set.pi (Set.univ : Set ℕ) fun j => closure (Set.range fun n => F n j)) :=
    isCompact_univ_pi hcompact
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (x := fun n j => F n j)
    (fun n j _ => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, a, hφ, fun j ε hε => ?_⟩
  have hj := tendsto_pi_nhds.1 hlim j
  rw [Metric.tendsto_atTop] at hj
  obtain ⟨N, hN⟩ := hj ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with k hk τ
  have := hN k hk
  have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := F (φ k) j) (g := a j) τ
  rw [Real.dist_eq] at h2
  rw [← hF]
  exact h2.trans this.le

end Aux

-- BEGIN SA12.L4
theorem hilbert_path_compact
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SecondCountableTopology H]
    (e : ℕ → H) (he : DenseRange e) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (u : ℕ → ℝ → H) (hu : ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, ‖u n τ‖ ≤ B)
    (hequi : ∀ j, ∃ K : ℝ, ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, ∀ σ ∈ Icc (0 : ℝ) T,
      |inner ℝ (u n τ - u n σ) (e j)| ≤ K * |τ - σ|) :
    ∃ (n : ℕ → ℕ) (v : ℝ → H), StrictMono n ∧
      (∀ τ ∈ Icc (0 : ℝ) T, ‖v τ‖ ≤ B) ∧
      (∀ h : H, ContinuousOn (fun τ => inner ℝ (v τ) h) (Icc (0 : ℝ) T)) ∧
      ∀ h : H, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ τ ∈ Icc (0 : ℝ) T,
        |inner ℝ (u (n k) τ - v τ) h| ≤ ε := by
  obtain ⟨φ, a, hφ, ha⟩ := sa12x_extract e B T u hu hequi
  -- the weak limit at each time
  have hex : ∀ τ : ℝ, ∃ w : H, τ ∈ Icc (0 : ℝ) T →
      ‖w‖ ≤ B ∧ ∀ h : H, Tendsto (fun k => inner ℝ (u (φ k) τ) h) atTop (𝓝 (inner ℝ w h)) := by
    intro τ
    by_cases hτ : τ ∈ Icc (0 : ℝ) T
    · have hl : ∀ j, Tendsto (fun k => inner ℝ (u (φ k) τ) (e j)) atTop (𝓝 (a j ⟨τ, hτ⟩)) := by
        intro j
        rw [Metric.tendsto_nhds]
        intro ε hε
        filter_upwards [ha j (ε / 2) (half_pos hε)] with k hk
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hk ⟨τ, hτ⟩) (half_lt_self hε)
      obtain ⟨w, hw1, hw2⟩ := sa12x_weak_limit e he B hB (fun k => u (φ k) τ)
        (fun k => hu (φ k) τ hτ) (fun j => a j ⟨τ, hτ⟩) hl
      exact ⟨w, fun _ => ⟨hw1, hw2⟩⟩
    · exact ⟨0, fun h => absurd h hτ⟩
  choose v hv using hex
  have hvj : ∀ j, ∀ (τ : Icc (0 : ℝ) T), inner ℝ (v τ) (e j) = a j τ := by
    intro j τ
    have h1 := (hv τ τ.2).2 (e j)
    have h2 : Tendsto (fun k => inner ℝ (u (φ k) τ) (e j)) atTop (𝓝 (a j τ)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [ha j (ε / 2) (half_pos hε)] with k hk
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hk τ) (half_lt_self hε)
    exact tendsto_nhds_unique h1 h2
  refine ⟨φ, v, hφ, fun τ hτ => (hv τ hτ).1, fun h => ?_, fun h ε hε => ?_⟩
  · rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨j, hj⟩ := he.exists_dist_lt h (show 0 < ε / (4 * (B + 1)) by positivity)
    have hjc : ContinuousOn (fun τ => inner ℝ (v τ) (e j)) (Icc (0 : ℝ) T) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (Set.domRestrict (Icc (0 : ℝ) T) fun τ => inner ℝ (v τ) (e j)) = fun τ => a j τ :=
        funext fun τ => hvj j τ
      rw [this]
      exact (a j).continuous
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousOn_iff.1 hjc b hb (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun c hc hcb => ?_⟩
    have h1 := hδ' c hc hcb
    rw [Real.dist_eq] at h1 ⊢
    have h2 : inner ℝ (v c) h - inner ℝ (v b) h =
        (inner ℝ (v c) (e j) - inner ℝ (v b) (e j)) + inner ℝ (v c - v b) (h - e j) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    have hn' : ‖h - e j‖ ≤ ε / (4 * (B + 1)) := by rw [← dist_eq_norm]; exact hj.le
    have h3 : |inner ℝ (v c - v b) (h - e j)| ≤ 2 * B * (ε / (4 * (B + 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have : ‖v c - v b‖ ≤ 2 * B := by
        have := norm_sub_le (v c) (v b); linarith [(hv c hc).1, (hv b hb).1]
      exact mul_le_mul this hn' (norm_nonneg _) (by linarith)
    have h4 : 2 * B * (ε / (4 * (B + 1))) ≤ ε / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    rw [h2]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    linarith
  · obtain ⟨j, hj⟩ := he.exists_dist_lt h (show 0 < ε / (4 * (B + 1)) by positivity)
    filter_upwards [ha j (ε / 2) (half_pos hε)] with k hk τ hτ
    have h2 : inner ℝ (u (φ k) τ - v τ) h =
        inner ℝ (u (φ k) τ - v τ) (e j) + inner ℝ (u (φ k) τ - v τ) (h - e j) := by
      simp only [inner_sub_right]; ring
    have hn' : ‖h - e j‖ ≤ ε / (4 * (B + 1)) := by rw [← dist_eq_norm]; exact hj.le
    have h3 : |inner ℝ (u (φ k) τ - v τ) (h - e j)| ≤ 2 * B * (ε / (4 * (B + 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have : ‖u (φ k) τ - v τ‖ ≤ 2 * B := by
        have := norm_sub_le (u (φ k) τ) (v τ); linarith [hu (φ k) τ hτ, (hv τ hτ).1]
      exact mul_le_mul this hn' (norm_nonneg _) (by linarith)
    have h4 : 2 * B * (ε / (4 * (B + 1))) ≤ ε / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 : inner ℝ (u (φ k) τ - v τ) (e j) = inner ℝ (u (φ k) τ) (e j) - a j ⟨τ, hτ⟩ := by
      rw [inner_sub_left, hvj j ⟨τ, hτ⟩]
    have h6 := hk ⟨τ, hτ⟩
    rw [h2]
    refine (abs_add_le _ _).trans ?_
    rw [h5]
    linarith
-- END SA12.L4

end HRS.MH.AdjointRd.Phase2SA12Limit
