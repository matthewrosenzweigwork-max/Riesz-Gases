import HRS.Uniform.Q45Cov4

/-!
# Q45 (Lemma 3.20): Riemann sums of cell integrals converge (dominated convergence)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Cells

lemma mem_cell_iff {t : ℝ} (ht : 0 < t) {M : ℝ} (hM : 0 < M) (j : ℕ) {σ : ℝ} :
    σ ∈ Set.Ioc (t * j / M) (t * (j + 1) / M) ↔ (j : ℝ) < σ * M / t ∧ σ * M / t ≤ j + 1 := by
  simp only [Set.mem_Ioc]
  rw [div_lt_iff₀ hM, le_div_iff₀ hM, lt_div_iff₀ ht, div_le_iff₀ ht]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

lemma cells_tendsto {t : ℝ} (ht : 0 < t) {Φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ}
    (hmeas : ∀ s, Measurable (fun σ => Φ σ s))
    (hbound : ∀ σ ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, |Φ σ s| ≤ β σ)
    (hβ : IntegrableOn β (Set.Icc 0 t))
    (hcont : ∀ σ ∈ Set.Ioc 0 t, ContinuousWithinAt (Φ σ) (Set.Icc 0 t) σ) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1),
        ∫ σ in Set.Icc (t * i / ((N : ℝ) + 1)) (t * (i + 1) / ((N : ℝ) + 1)),
          Φ σ (t * i / ((N : ℝ) + 1)))
      atTop (𝓝 (∫ σ in Set.Icc 0 t, Φ σ σ)) ∧ IntegrableOn (fun σ => Φ σ σ) (Set.Icc 0 t) := by
  -- the nodes
  set a : ℕ → ℕ → ℝ := fun N i => t * i / ((N : ℝ) + 1) with ha
  have hMpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  have ha0 : ∀ N i, 0 ≤ a N i := fun N i => by simp only [ha]; positivity
  have haN : ∀ N, a N (N + 1) = t := fun N => by
    simp only [ha]
    push_cast
    field_simp
  have ha_mono : ∀ N, Monotone (a N) := fun N i j hij => by
    simp only [ha]
    gcongr
  have ha_le : ∀ N i, i ≤ N + 1 → a N i ≤ t := fun N i hi => by
    calc a N i ≤ a N (N + 1) := ha_mono N hi
      _ = t := haN N
  have hcell_sub : ∀ N i, i < N + 1 → Set.Ioc (a N i) (a N (i + 1)) ⊆ Set.Ioc 0 t := fun N i hi σ hσ =>
    ⟨lt_of_le_of_lt (ha0 N i) hσ.1, hσ.2.trans (ha_le N (i + 1) hi)⟩
  -- the step functions
  set F : ℕ → ℝ → ℝ := fun N σ => ∑ i ∈ Finset.range (N + 1),
    (Set.Ioc (a N i) (a N (i + 1))).indicator (fun σ => Φ σ (a N i)) σ with hF
  have hFmeas : ∀ N, Measurable (F N) := fun N =>
    Finset.measurable_sum _ fun i _ => (hmeas _).indicator measurableSet_Ioc
  -- value of `F N` at a point of `(0,t]`
  have hFval : ∀ N, ∀ σ ∈ Set.Ioc 0 t, ∃ i, i < N + 1 ∧ σ ∈ Set.Ioc (a N i) (a N (i + 1)) ∧
      F N σ = Φ σ (a N i) := by
    intro N σ hσ
    have hM := hMpos N
    set x : ℝ := σ * ((N : ℝ) + 1) / t with hx
    have hx0 : 0 < x := by simp only [hx]; have := hσ.1; positivity
    have hxN : x ≤ (N : ℝ) + 1 := by
      simp only [hx]; rw [div_le_iff₀ ht]; nlinarith [hσ.2]
    set i : ℕ := ⌈x⌉₊ - 1 with hi
    have hc1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx0).ne'
    have hxi1 : x ≤ (i : ℝ) + 1 := by
      have : ((i : ℕ) : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by
        simp only [hi]; rw [Nat.cast_sub hc1]; ring
      rw [this]; exact Nat.le_ceil x
    have hxi0 : (i : ℝ) < x := by
      have h := Nat.ceil_lt_add_one hx0.le
      have : ((i : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by simp only [hi]; rw [Nat.cast_sub hc1]; simp
      rw [this]; linarith
    have hiN : i < N + 1 := by
      have : ⌈x⌉₊ ≤ N + 1 := Nat.ceil_le.2 (by exact_mod_cast hxN)
      simp only [hi]; omega
    have hmem : σ ∈ Set.Ioc (a N i) (a N (i + 1)) := by
      simp only [ha]
      push_cast
      rw [mem_cell_iff ht hM]
      exact ⟨hxi0, hxi1⟩
    refine ⟨i, hiN, hmem, ?_⟩
    simp only [hF]
    rw [Finset.sum_eq_single i]
    · simp [Set.indicator_of_mem hmem]
    · intro j _ hji
      have hj : σ ∉ Set.Ioc (a N j) (a N (j + 1)) := by
        intro hj
        simp only [ha] at hj
        push_cast at hj
        rw [mem_cell_iff ht hM] at hj
        have hj1 : (⌈x⌉₊ : ℕ) = j + 1 := by
          rw [Nat.ceil_eq_iff (by omega)]
          constructor
          · push_cast; linarith [hj.1]
          · push_cast; exact hj.2
        omega
      simp [Set.indicator_of_notMem hj]
    · intro h; exact absurd (Finset.mem_range.2 hiN) h
  -- the integrals over the cells add up
  have hint_cell : ∀ N i, i < N + 1 →
      Integrable ((Set.Ioc (a N i) (a N (i + 1))).indicator (fun σ => Φ σ (a N i)))
        (volume.restrict (Set.Ioc 0 t)) := by
    intro N i hi
    have hsub := hcell_sub N i hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hI : IntegrableOn (fun σ => Φ σ (a N i)) (Set.Ioc (a N i) (a N (i + 1))) volume := by
      refine Integrable.mono' (hβ.mono_set (hsub.trans Set.Ioc_subset_Icc_self)) ?_ ?_
      · exact ((hmeas _).aestronglyMeasurable)
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ => ?_)
        have hσ' : σ ∈ Set.Icc 0 t := Set.Ioc_subset_Icc_self (hsub hσ)
        have hs : a N i ∈ Set.Icc 0 t := ⟨ha0 N i, ha_le N i (by omega)⟩
        simpa [Real.norm_eq_abs] using hbound σ hσ' (a N i) hs
    exact hI.restrict
  have hsumeq : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1),
        ∫ σ in Set.Icc (t * i / ((N : ℝ) + 1)) (t * (i + 1) / ((N : ℝ) + 1)),
          Φ σ (t * i / ((N : ℝ) + 1)) = ∫ σ in Set.Ioc 0 t, F N σ := by
    intro N
    simp only [hF]
    rw [integral_finsetSum _ (fun i hi => hint_cell N i (Finset.mem_range.1 hi))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsub := hcell_sub N i (Finset.mem_range.1 hi)
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.2 hsub,
      integral_Icc_eq_integral_Ioc]
    simp only [ha, Nat.cast_add, Nat.cast_one]
  simp_rw [hsumeq]
  have hI : ∫ σ in Set.Icc 0 t, Φ σ σ = ∫ σ in Set.Ioc 0 t, Φ σ σ := integral_Icc_eq_integral_Ioc
  rw [hI]
  have hbd : ∀ N : ℕ, ∀ᵐ σ ∂(volume.restrict (Set.Ioc 0 t)), ‖F N σ‖ ≤ β σ := fun N => by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ => ?_)
    obtain ⟨i, hi, hmem, hval⟩ := hFval N σ hσ
    rw [hval, Real.norm_eq_abs]
    exact hbound σ (Set.Ioc_subset_Icc_self hσ) _ ⟨ha0 N i, ha_le N i (by omega)⟩
  have hlimae : ∀ᵐ σ ∂(volume.restrict (Set.Ioc 0 t)), Tendsto (fun N => F N σ) atTop (𝓝 (Φ σ σ)) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ => ?_)
    have h := fun N : ℕ => hFval N σ hσ
    choose i hi hmem hval using h
    have hdiff : ∀ N : ℕ, a N (i N + 1) - a N (i N) = t / ((N : ℝ) + 1) := fun N => by
      simp only [ha]
      have := hMpos N
      push_cast
      field_simp
      ring
    have hlow : ∀ N : ℕ, σ - t / ((N : ℝ) + 1) ≤ a N (i N) := fun N => by
      have := (hmem N).2
      have := hdiff N
      linarith
    have hup : ∀ N : ℕ, a N (i N) ≤ σ := fun N => ((hmem N).1).le
    have hlim0 : Tendsto (fun N : ℕ => t / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat t |>.comp (tendsto_add_atTop_nat 1) |> fun h => by
        simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
    have hlimA : Tendsto (fun N => a N (i N)) atTop (𝓝 σ) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun N : ℕ => σ - t / ((N : ℝ) + 1))
        (h := fun _ => σ) ?_ tendsto_const_nhds hlow hup
      simpa using (tendsto_const_nhds (x := σ)).sub hlim0
    have hmemI : ∀ N : ℕ, a N (i N) ∈ Set.Icc 0 t := fun N => ⟨ha0 N _, ha_le N _ (by have := hi N; omega)⟩
    have h2 : Tendsto (fun N => a N (i N)) atTop (𝓝[Set.Icc 0 t] σ) :=
      tendsto_nhdsWithin_iff.2 ⟨hlimA, Eventually.of_forall hmemI⟩
    have h3 := (hcont σ hσ).tendsto.comp h2
    refine h3.congr fun N => ?_
    simp only [Function.comp_apply]
    exact (hval N).symm

  have hint : Integrable (fun σ => Φ σ σ) (volume.restrict (Set.Ioc 0 t)) := by
    refine Integrable.mono' (hβ.mono_set Set.Ioc_subset_Icc_self)
      (aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hFmeas N).aestronglyMeasurable) hlimae) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs]
    exact hbound σ (Set.Ioc_subset_Icc_self hσ) σ (Set.Ioc_subset_Icc_self hσ)
  refine ⟨?_, ?_⟩
  · refine tendsto_integral_of_dominated_convergence (fun σ => β σ)
      (fun N => (hFmeas N).aestronglyMeasurable) (hβ.mono_set Set.Ioc_subset_Icc_self) hbd hlimae
  · exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hint

end Cells

end HRS.Uniform.Q45
