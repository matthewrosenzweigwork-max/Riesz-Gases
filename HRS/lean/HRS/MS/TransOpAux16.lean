import HRS.MS.TransOpAux13

/-!
# S611 packet P2g: strong and joint continuity of `Λ_c`

`s611_Lam_tendsto_left`: `c ↦ Λ_c u` is continuous for every `u ∈ B_m`;
`s611_Lam_tendsto`: if `c_i → c₀`, `u_i → u₀` along a filter then `Λ_{c_i} u_i → Λ_{c₀} u₀`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_single_eq (M : ℝ) (β : MultiIndex d) (a : ℝ) :
    (lp.single 2 β a : lp (fun _ : MultiIndex d => ℝ) 2) = a • (s611_e1 M β : lp (fun _ : MultiIndex d => ℝ) 2) := by
  unfold s611_e1
  have := lp.single_smul (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 β a (1 : ℝ)
  rw [smul_eq_mul, mul_one] at this
  exact this

theorem s611_Lam_tendsto_left (m : ℕ) (hm : 1 ≤ m) (c₀ : Euc d) (u : OscDual d (m : ℝ)) :
    Tendsto (fun c : Euc d => s611_Lam m hm c u) (𝓝 c₀) (𝓝 (s611_Lam m hm c₀ u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Kb : ℝ := s611_K m c₀ + 1 with hKb
  have hKb0 : 0 < Kb := by have := s611_K_pos (d := d) m c₀; rw [hKb]; linarith
  have hK : ∀ᶠ c in 𝓝 c₀, s611_K m c < Kb :=
    ((s611_K_continuous (d := d) m).tendsto c₀).eventually
      (Iio_mem_nhds (by rw [hKb]; linarith))
  set δ : ℝ := ε / (3 * Kb) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsum := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from u)
  obtain ⟨F, hF⟩ := (hsum.eventually (Metric.ball_mem_nhds _ hδ0)).exists
  set uF : OscDual d (m : ℝ) :=
    ∑ β ∈ F, (OscDual.coord u β) • (s611_e1 (m : ℝ) β) with huF
  have huFdist : ‖u - uF‖ < δ := by
    have h1 : dist (∑ β ∈ F, lp.single 2 β ((show lp (fun _ : MultiIndex d => ℝ) 2 from u) β))
        (show lp (fun _ : MultiIndex d => ℝ) 2 from u) < δ := hF
    have h2 : (∑ β ∈ F, lp.single 2 β ((show lp (fun _ : MultiIndex d => ℝ) 2 from u) β)) =
        (show lp (fun _ : MultiIndex d => ℝ) 2 from uF) := by
      rw [huF]
      simp_rw [s611_single_eq (m : ℝ)]
      rfl
    rw [h2, dist_comm, dist_eq_norm] at h1
    exact h1
  have hmid : ∀ᶠ c in 𝓝 c₀, ‖s611_Lam m hm c uF - s611_Lam m hm c₀ uF‖ < ε / 3 := by
    have ht : Tendsto (fun c : Euc d => s611_Lam m hm c uF) (𝓝 c₀) (𝓝 (s611_Lam m hm c₀ uF)) := by
      have : (fun c : Euc d => s611_Lam m hm c uF) =
          fun c => ∑ β ∈ F, (OscDual.coord u β) • s611_Lam m hm c (s611_e1 (m : ℝ) β) := by
        funext c
        rw [huF, map_sum]
        simp only [map_smul]
      rw [this]
      have : s611_Lam m hm c₀ uF = ∑ β ∈ F, (OscDual.coord u β) • s611_Lam m hm c₀ (s611_e1 (m : ℝ) β) := by
        rw [huF, map_sum]
        simp only [map_smul]
      rw [this]
      exact tendsto_finsetSum _ fun β _ => (s611_Lam_e1_tendsto m hm β c₀).const_smul _
    have := (tendsto_iff_norm_sub_tendsto_zero.1 ht)
    exact this.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hK, hmid] with c hc1 hc2
  rw [dist_eq_norm]
  have e : s611_Lam m hm c u - s611_Lam m hm c₀ u =
      s611_Lam m hm c (u - uF) + (s611_Lam m hm c uF - s611_Lam m hm c₀ uF) +
        s611_Lam m hm c₀ (uF - u) := by
    simp only [map_sub]; abel
  rw [e]
  have b1 : ‖s611_Lam m hm c (u - uF)‖ ≤ Kb * δ :=
    ((s611_Lam m hm c).le_opNorm _).trans
      (mul_le_mul ((s611_norm_Lam_le m hm c).trans hc1.le) huFdist.le (norm_nonneg _) hKb0.le)
  have b3 : ‖s611_Lam m hm c₀ (uF - u)‖ ≤ Kb * δ := by
    refine ((s611_Lam m hm c₀).le_opNorm _).trans
      (mul_le_mul ((s611_norm_Lam_le m hm c₀).trans (by rw [hKb]; linarith)) ?_ (norm_nonneg _) hKb0.le)
    rw [norm_sub_rev]; exact huFdist.le
  have hKd : Kb * δ = ε / 3 := by rw [hδ]; field_simp
  calc ‖s611_Lam m hm c (u - uF) + (s611_Lam m hm c uF - s611_Lam m hm c₀ uF) +
        s611_Lam m hm c₀ (uF - u)‖
      ≤ ‖s611_Lam m hm c (u - uF) + (s611_Lam m hm c uF - s611_Lam m hm c₀ uF)‖ +
          ‖s611_Lam m hm c₀ (uF - u)‖ := norm_add_le _ _
    _ ≤ (‖s611_Lam m hm c (u - uF)‖ + ‖s611_Lam m hm c uF - s611_Lam m hm c₀ uF‖) +
          ‖s611_Lam m hm c₀ (uF - u)‖ := by gcongr; exact norm_add_le _ _
    _ < ε := by linarith

theorem s611_Lam_tendsto (m : ℕ) (hm : 1 ≤ m) {ι : Type*} {l : Filter ι} {c : ι → Euc d}
    {u : ι → OscDual d (m : ℝ)} {c₀ : Euc d} {u₀ : OscDual d (m : ℝ)}
    (hc : Tendsto c l (𝓝 c₀)) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => s611_Lam m hm (c i) (u i)) l (𝓝 (s611_Lam m hm c₀ u₀)) := by
  set Kb : ℝ := s611_K m c₀ + 1 with hKb
  have hK : ∀ᶠ i in l, s611_K m (c i) < Kb :=
    (((s611_K_continuous (d := d) m).tendsto c₀).comp hc).eventually
      (Iio_mem_nhds (by rw [hKb]; linarith))
  have h1 : Tendsto (fun i => s611_Lam m hm (c i) u₀) l (𝓝 (s611_Lam m hm c₀ u₀)) :=
    (s611_Lam_tendsto_left m hm c₀ u₀).comp hc
  have h2 : Tendsto (fun i => ‖u i - u₀‖) l (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hu)
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h3 : Tendsto (fun i => ‖s611_Lam m hm (c i) u₀ - s611_Lam m hm c₀ u₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 h1
  have h4 : Tendsto (fun i => Kb * ‖u i - u₀‖ + ‖s611_Lam m hm (c i) u₀ - s611_Lam m hm c₀ u₀‖) l (𝓝 0) := by
    have := (h2.const_mul Kb).add h3
    simpa using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ h4
  filter_upwards [hK] with i hi
  have e : s611_Lam m hm (c i) (u i) - s611_Lam m hm c₀ u₀ =
      s611_Lam m hm (c i) (u i - u₀) + (s611_Lam m hm (c i) u₀ - s611_Lam m hm c₀ u₀) := by
    simp only [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact ((s611_Lam m hm (c i)).le_opNorm _).trans
    (mul_le_mul ((s611_norm_Lam_le m hm (c i)).trans hi.le) le_rfl (norm_nonneg _)
      (by have := s611_K_pos (d := d) m c₀; rw [hKb]; linarith))

end HRS.MS.TransOp

end
