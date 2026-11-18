import HRS.MC.CepE6aA1

/-!
# Packet CEPE6A, file 2: the limit process from a Cauchy-in-probability sequence

From the Cauchy property in probability (E5c) we extract a fast subsequence `k j` (with `m j ≤ k j` for any prescribed
thresholds `m`), a null set `Gᶜ`, and an adapted continuous limit `Zl` with `Z (k j) → Zl` locally uniformly on `G`,
and then the whole sequence converges to `Zl` uniformly on `[0,T]` in probability.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem e6a_le_iSup {f : ℝ → ℝ} (hf : Continuous f) {T t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    f t ≤ ⨆ s : Icc (0 : ℝ) T, f s := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hf.continuousOn
  exact le_ciSup (f := fun s : Icc (0 : ℝ) T => f s) ⟨M, by rintro _ ⟨s, rfl⟩; exact hM ⟨s, s.2, rfl⟩⟩ ⟨t, ht⟩

theorem e6a_iSup_le {f : ℝ → ℝ} {T c : ℝ} (hc : 0 ≤ c) (h : ∀ t ∈ Icc (0 : ℝ) T, f t ≤ c) :
    (⨆ s : Icc (0 : ℝ) T, f s) ≤ c := by
  rcases isEmpty_or_nonempty (Icc (0 : ℝ) T) with hE | hE
  · simp [hc]
  · exact ciSup_le fun s => h s s.2

/-- The data produced from the Cauchy property in probability. -/
theorem e6a_limit_exists [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} (hℱ : IsCompleteFiltration P ℱ)
    {Z : ℕ → ℝ → Ω → Ch N} (hZc : ∀ n ω, Continuous fun t => Z n t ω)
    (hZm : ∀ n t, 0 ≤ t → Measurable[ℱ t] (Z n t))
    (hcau : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ ≤ m → n₀ ≤ n →
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} < ENNReal.ofReal ε)
    (m : ℕ → ℕ) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ j, m j ≤ k j) ∧ (∀ j, j ≤ k j) ∧
      ∃ (Zl : ℝ → Ω → Ch N) (G : Set Ω), (∀ ω, Continuous fun t => Zl t ω) ∧
        (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧ MeasurableSet G ∧ P Gᶜ = 0 ∧
        (∀ ω ∈ G, ∀ T : ℕ, TendstoUniformlyOn (fun j t => Z (k j) t ω) (fun t => Zl t ω) atTop
          (Icc (0 : ℝ) T)) ∧
        (∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
          P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) atTop (𝓝 0)) := by
  classical
  -- thresholds
  have hex : ∀ j : ℕ, ∃ n₀ : ℕ, ∀ m' n : ℕ, n₀ ≤ m' → n₀ ≤ n →
      P {ω | (1 / 2 : ℝ) ^ j < ⨆ t : Set.Icc (0 : ℝ) (j : ℝ), ‖Z m' t ω - Z n t ω‖} <
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := fun j => hcau (j : ℝ) ((1 / 2 : ℝ) ^ j) (by positivity)
  choose n₀ hn₀ using hex
  set m' : ℕ → ℕ := fun j => max (n₀ j) (max (m j) j) with hm'
  set k : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), (m' i + 1) with hk
  have hkmono : StrictMono k := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [hk, Finset.sum_range_succ _ (j + 1)]
    omega
  have hkm : ∀ j, m' j ≤ k j := by
    intro j
    have : m' j + 1 ≤ k j := by
      simp only [hk]
      exact Finset.single_le_sum (f := fun i => m' i + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_self j))
    omega
  have hkn : ∀ j, n₀ j ≤ k j := fun j => (le_max_left _ _).trans (hkm j)
  have hkm2 : ∀ j, m j ≤ k j := fun j => ((le_max_left _ _).trans (le_max_right _ _)).trans (hkm j)
  have hkj : ∀ j, j ≤ k j := fun j => ((le_max_right _ _).trans (le_max_right _ _)).trans (hkm j)
  -- bad events
  set A : ℕ → Set Ω := fun j => {ω | (1 / 2 : ℝ) ^ j <
    ⨆ t : Set.Icc (0 : ℝ) (j : ℝ), ‖Z (k (j + 1)) t ω - Z (k j) t ω‖} with hA
  have hPA : ∀ j, P (A j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j
    have h := hn₀ j (k (j + 1)) (k j) ((hkn j).trans (hkmono.monotone (Nat.le_succ j))) (hkn j)
    refine h.le.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hsum : ∑' j, P (A j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hPA)
    rw [ENNReal.tsum_geometric]
    simp
  have hae := ae_eventually_notMem hsum
  set G0 : Set Ω := {ω | ∀ᶠ l in atTop, ω ∉ A l} with hG0
  have hG0c : P G0ᶜ = 0 := by
    exact ae_iff.1 hae
  set N0 : Set Ω := toMeasurable P G0ᶜ with hN0
  set G : Set Ω := N0ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGnull : P Gᶜ = 0 := by
    rw [hG, compl_compl, hN0, measure_toMeasurable]; exact hG0c
  have hGsub : ∀ ω ∈ G, ω ∈ G0 := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  -- fast Cauchy on `G`
  have hfast : ∀ ω ∈ G, ∀ T : ℕ, ∃ J : ℕ, ∀ l, J ≤ l → ∀ t ∈ Icc (0 : ℝ) T,
      ‖Z (k (l + 1)) t ω - Z (k l) t ω‖ ≤ (1 / 2 : ℝ) ^ l := by
    intro ω hω T
    have h1 := hGsub ω hω
    simp only [hG0, mem_setOf_eq] at h1
    obtain ⟨J1, hJ1⟩ := eventually_atTop.1 h1
    refine ⟨max J1 T, fun l hl t ht => ?_⟩
    have hl1 : J1 ≤ l := (le_max_left _ _).trans hl
    have hlT : (T : ℝ) ≤ l := by exact_mod_cast (le_max_right _ _).trans hl
    have hnA : ω ∉ A l := hJ1 l hl1
    simp only [hA, mem_setOf_eq, not_lt] at hnA
    have hle := e6a_le_iSup (f := fun t => ‖Z (k (l + 1)) t ω - Z (k l) t ω‖)
      (((hZc _ ω).sub (hZc _ ω)).norm) (T := (l : ℝ)) (t := t) ⟨ht.1, ht.2.trans hlT⟩
    exact hle.trans hnA
  obtain ⟨Zl, hZlc, hZlm, hZlu⟩ := e6a_exists_limit hℱ (Y := fun j => Z (k j))
    (fun j ω => hZc _ ω) (fun j t ht => hZm _ t ht) hGm hGnull hfast
  refine ⟨k, hkmono, hkm2, hkj, Zl, G, hZlc, hZlm, hGm, hGnull, hZlu, ?_⟩
  -- convergence in probability of the whole sequence
  intro T ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨r, hr0, hrη⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ η := by
    rcases eq_or_ne η ∞ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨η.toReal, ENNReal.toReal_pos hη.ne' hne, ?_⟩
      rw [ENNReal.ofReal_toReal hne]
  set ε' : ℝ := min ε r with hε'
  have hε'0 : 0 < ε' := lt_min hε hr0
  obtain ⟨n₁, hn₁⟩ := hcau T ε' hε'0
  obtain ⟨T', hT'⟩ := exists_nat_ge T
  filter_upwards [eventually_ge_atTop n₁] with n hn
  -- the event is contained in an increasing union
  set B : ℕ → Set Ω := fun j => {ω | ε' < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Z (k j) t ω‖} with hB
  set C : ℕ → Set Ω := fun J => ⋂ j ∈ {j | J ≤ j}, B j with hC
  have hsub : {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖} ⊆ (⋃ J, C J) ∪ Gᶜ := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · left
      simp only [mem_setOf_eq] at hω
      have hex : ∃ t ∈ Icc (0 : ℝ) T, ε' < ‖Z n t ω - Zl t ω‖ := by
        by_contra hcon
        push_neg at hcon
        have := e6a_iSup_le (f := fun t => ‖Z n t ω - Zl t ω‖) (T := T) (c := ε') hε'0.le hcon
        have h2 : ε' ≤ ε := min_le_left _ _
        linarith
      obtain ⟨t, ht, htε⟩ := hex
      have hconv : Tendsto (fun j => Z (k j) t ω) atTop (𝓝 (Zl t ω)) := by
        have := (hZlu ω hωG T').tendsto_at (x := t) ⟨ht.1, ht.2.trans hT'⟩
        exact this
      have hev : ∀ᶠ j in atTop, ε' < ‖Z n t ω - Z (k j) t ω‖ := by
        have h3 : Tendsto (fun j => ‖Z n t ω - Z (k j) t ω‖) atTop (𝓝 ‖Z n t ω - Zl t ω‖) :=
          (tendsto_const_nhds.sub hconv).norm
        exact h3.eventually (lt_mem_nhds htε)
      obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
      refine mem_iUnion.2 ⟨J, ?_⟩
      simp only [hC, mem_iInter]
      intro j hj
      have hj' : J ≤ j := hj
      show ω ∈ B j
      simp only [hB, mem_setOf_eq]
      refine lt_of_lt_of_le (hJ j hj') ?_
      exact e6a_le_iSup (f := fun t => ‖Z n t ω - Z (k j) t ω‖) (((hZc _ ω).sub (hZc _ ω)).norm) ht
    · right; exact hωG
  have hmono : Monotone C := by
    intro J J' hJJ'
    simp only [hC]
    exact biInter_subset_biInter_left fun j hj => le_trans hJJ' hj
  have hCle : ∀ J, P (C J) ≤ ENNReal.ofReal ε' := by
    intro J
    have hj0 : J + n₁ ≤ k (J + n₁) := hkj _
    have hmem : C J ⊆ B (J + n₁) := by
      intro ω hω
      simp only [hC, mem_iInter] at hω
      exact hω (J + n₁) (by simp)
    exact (measure_mono hmem).trans (hn₁ n (k (J + n₁)) hn (by omega)).le
  have hU : P (⋃ J, C J) ≤ ENNReal.ofReal ε' := by
    rw [hmono.measure_iUnion]
    exact iSup_le hCle
  calc P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}
      ≤ P ((⋃ J, C J) ∪ Gᶜ) := measure_mono hsub
    _ ≤ P (⋃ J, C J) + P Gᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ε' + 0 := by rw [hGnull]; exact add_le_add hU le_rfl
    _ ≤ η := by
      rw [add_zero]
      exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans hrη

end HRS.MC.CepE6A
