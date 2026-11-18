import HRS.MS.WadAux180

/-!
# S8.3, packet S8H2-7: continuity in time of the semigroup and of `tensorU`

For `φ ∈ C_c^∞` the map `t ↦ U_tφ(x)` is continuous on `[0,∞)` (`s8h2_U_cont`; `U_sφ = f(T-s)` for the classical solution `f` on `[0,T]`,
by time shift and uniqueness); hence so is `t ↦ tensorU U t G z` for separated `G` (`s8h2_S_sep_cont`) and, as a uniform limit on `[0,T]`
(`s8h2_P1`), for every `F` with `S8hPair M j F` (`s8h2_S_cont`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_contOn_Ici_of_Icc {f : ℝ → ℝ} (h : ∀ T : ℝ, ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn f (Set.Ici 0) := by
  intro t ht
  have h1 : ContinuousWithinAt f (Set.Icc 0 (t + 1)) t := h (t + 1) t ⟨ht, by linarith [ht.out]⟩
  refine h1.mono_of_mem_nhdsWithin ?_
  have h2 : Set.Iio (t + 1) ∈ 𝓝 t := Iio_mem_nhds (by linarith)
  filter_upwards [inter_mem_nhdsWithin (Set.Ici 0) h2] with s hs
  exact ⟨hs.1, hs.2.le⟩

theorem s8h2_gen_time (a β : ℝ) (ρβ : Euc d → ℝ) (r r' : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) r h x =
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) r' h x := by
  unfold projGeneratorW
  simp only [s85_gen_time a β ρβ r r' h]

section Interface

variable {a β : ℝ} {ρβ : Euc d → ℝ} {M : ℝ} {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s8h2_U_eq_sol (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {T s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) {f : ℝ → Euc d → ℝ}
    (hf : IsAdjointSolutionG (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ)) T φ f) :
    U s φ = f (T - s) := by
  have hg : IsAdjointSolutionG (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ)) s φ
      (fun r => f (r + (T - s))) := by
    refine s85_G_shift (fun r r' h x => s8h2_gen_time a β ρβ r r' h x) (t := T - s) (s := s)
      (by linarith) hs ?_
    rwa [show T - s + s = T by ring]
  obtain ⟨f', hf', hUf'⟩ := hU.classical s hs φ hφ.1 hφ.2
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ hs hφ
  funext x
  rw [hUf', s85_proj_unique hd ha hβ hρ hs hf' hw x]
  have := s85_proj_unique hd ha hβ hρ hs hg hw x
  rw [← this]
  simp

theorem s8h2_U_cont (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {φ : Euc d → ℝ} (hφ : S85Cc φ) (x : Euc d) : ContinuousOn (fun t => U t φ x) (Set.Ici 0) := by
  refine s8h2_contOn_Ici_of_Icc fun T => ?_
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨f, hf, -⟩ := hU.classical T hT φ hφ.1 hφ.2
    obtain ⟨-, -, -, -, -, -, hc, -, -, -⟩ := s85_G_facts hf
    have h1 := s85_slice_cont hc x
    have h2 : ContinuousOn (fun s => f (T - s) x) (Set.Icc 0 T) :=
      h1.comp (continuousOn_const.sub continuousOn_id) (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    exact h2.congr (fun s hs => by rw [s8h2_U_eq_sol hd ha hβ hρ hU hs.1 hs.2 hφ hf])
  · rw [Set.Icc_eq_empty (by linarith)]
    exact continuousOn_empty _

theorem s8h2_S_sep_cont (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    {G : Euc d × Euc d → ℝ} (hG : S8hSepZ G) (z : Euc d × Euc d) :
    ContinuousOn (fun t => s8h2_S U t G z) (Set.Ici 0) := by
  obtain ⟨ι, _, a', b', hab, rfl⟩ := hG
  have h : ContinuousOn (fun t => ∑ l, U t (a' l) z.1 * U t (b' l) z.2) (Set.Ici 0) :=
    continuousOn_finset_sum _ fun l _ =>
      (s8h2_U_cont hd ha hβ hρ hU (hab l).1 z.1).mul (s8h2_U_cont hd ha hβ hρ hU (hab l).2 z.2)
  refine h.congr fun t ht => ?_
  exact s8h2_tensor_sep hU ht (fun l => (hab l).1) (fun l => (hab l).2) z.1 z.2

theorem s8h2_S_cont (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ)
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U)
    (h3 : S8eC3 M U) (hM : 0 ≤ M) {j : ℕ} {F : Euc d × Euc d → ℝ} (hF : S8hPair M j F)
    (z : Euc d × Euc d) : ContinuousOn (fun t => s8h2_S U t F z) (Set.Ici 0) := by
  refine s8h2_contOn_Ici_of_Icc fun T => ?_
  rcases le_or_gt 0 T with hT | hT
  swap
  · rw [Set.Icc_eq_empty (by linarith)]
    exact continuousOn_empty _
  obtain ⟨C, hC0, hP⟩ := s8h2_P1 hU h3 hM 0 hT
  obtain ⟨N0, -, G, hGs, -, hG⟩ := hP (s8h2_pair_mono (Nat.zero_le j) hF)
  have hcn : ∀ n, ContinuousOn (fun t => s8h2_S U t (G n) z) (Set.Icc 0 T) := fun n =>
    (s8h2_S_sep_cont hd ha hβ hρ hU (hGs n) z).mono Set.Icc_subset_Ici_self
  refine (TendstoUniformlyOn.continuousOn (F := fun n t => s8h2_S U t (G n) z) (p := atTop) ?_
    (Eventually.of_forall hcn).frequently)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hw := s8h_w_pos M z
  have hlim : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * C * s8h_w M z) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C |>.mul_const (s8h_w M z)
    simpa using this
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn t ht
  have h1 := (hG t ht).2.2 n 0 (Nat.zero_le 0) z
  rw [s8h_norm_iter0_sub] at h1
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  exact lt_of_le_of_lt h1 hn

end Interface

end HRS.MS.Wad
