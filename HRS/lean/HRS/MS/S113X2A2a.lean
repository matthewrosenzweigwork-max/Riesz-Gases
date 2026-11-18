import HRS.MS.S113X2A1j

/-!
# S11.3 X2 part A2a: two finite measures concentrated on an open set agreeing on `C_c(D)` are equal
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S113X2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An exhaustion of an open set by compact sets with Urysohn functions supported inside it. -/
theorem s113a_exhaustion {D : Set E} (hD : IsOpen D) :
    ∃ (K : ℕ → Set E) (χ : ℕ → E → ℝ), (∀ k, IsCompact (K k)) ∧ Monotone K ∧ (⋃ k, K k) = D ∧
      (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧ (∀ k, tsupport (χ k) ⊆ D) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ k, Set.EqOn (χ k) 1 (K k) := by
  obtain ⟨F, hFc, hFD, hFU, hFm⟩ := hD.exists_iUnion_isClosed
  let K : ℕ → Set E := fun k => F k ∩ Metric.closedBall 0 k
  have hKc : ∀ k, IsCompact (K k) := fun k => (isCompact_closedBall (0 : E) k).inter_left (hFc k)
  have hKD : ∀ k, K k ⊆ D := fun k => (Set.inter_subset_left).trans (hFD k)
  have hKm : Monotone K := fun a b hab =>
    Set.inter_subset_inter (hFm hab) (Metric.closedBall_subset_closedBall (by exact_mod_cast hab))
  have hKU : (⋃ k, K k) = D := by
    refine Set.Subset.antisymm (Set.iUnion_subset hKD) fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    obtain ⟨m, hm⟩ := exists_nat_ge (‖x‖)
    refine Set.mem_iUnion.2 ⟨max n m, ?_, ?_⟩
    · exact hFm (le_max_left _ _) hn
    · simp only [Metric.mem_closedBall, dist_zero_right]
      exact hm.trans (by exact_mod_cast le_max_right _ _)
  have key : ∀ k, ∃ f : C(E, ℝ), Set.EqOn f 1 (K k) ∧ HasCompactSupport f ∧ tsupport f ⊆ D ∧
      ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    obtain ⟨L, hLc, hKL, hLD⟩ := exists_compact_between (hKc k) hD (hKD k)
    obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact (hKc k)
      (isOpen_interior (s := L)).isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 hKL)
    refine ⟨f, hf1, hfc, ?_, hfI⟩
    have hs : Function.support f ⊆ interior L := by
      intro x hx
      by_contra h
      exact hx (hf0 h)
    have : tsupport f ⊆ L := by
      refine closure_minimal (hs.trans interior_subset) hLc.isClosed
    exact this.trans hLD
  choose f hf1 hfc hfD hfI using key
  exact ⟨K, fun k => f k, hKc, hKm, hKU, fun k => (f k).continuous, hfc, hfD,
    fun k x => hfI k x, hf1⟩

/-- Approximation of a bounded continuous integrand by its cutoffs, for a finite measure charging only `D`. -/
theorem s113a_cutoff_tendsto {D : Set E} {K : ℕ → Set E} {χ : ℕ → E → ℝ} (hKc : ∀ k, IsCompact (K k))
    (hKm : Monotone K) (hKU : (⋃ k, K k) = D) (hχc : ∀ k, Continuous (χ k))
    (hχI : ∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) (hχ1 : ∀ k, Set.EqOn (χ k) 1 (K k))
    (hχs : ∀ k, HasCompactSupport (χ k)) {ρ : Measure E} [IsFiniteMeasure ρ] (hρD : ρ Dᶜ = 0)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun k => ∫ x, f x * χ k x ∂ρ) atTop (𝓝 (∫ x, f x ∂ρ)) := by
  have hKmeas : ∀ k, MeasurableSet (K k) := fun k => (hKc k).isClosed.measurableSet
  have hcompl : Tendsto (fun k => ρ (K k)ᶜ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ρ (K k)) atTop (𝓝 (ρ (⋃ k, K k))) := tendsto_measure_iUnion_atTop hKm
    have h2 : ρ (⋃ k, K k) = ρ Set.univ := by
      rw [hKU]
      have : ρ D = ρ Set.univ := by
        have hD : D ∪ Dᶜ = Set.univ := Set.union_compl_self D
        have := measure_union_le (μ := ρ) D Dᶜ
        rw [hD, hρD, add_zero] at this
        exact le_antisymm (measure_mono (Set.subset_univ _)) this
      exact this
    rw [h2] at h1
    have h3 : ∀ k, ρ (K k)ᶜ = ρ Set.univ - ρ (K k) := fun k => measure_compl (hKmeas k) (measure_ne_top _ _)
    simp_rw [h3]
    have := ENNReal.Tendsto.sub tendsto_const_nhds h1 (Or.inl (measure_ne_top ρ Set.univ))
    simpa using this
  have hbound : ∀ k, ‖∫ x, f x * χ k x ∂ρ - ∫ x, f x ∂ρ‖ ≤ C * (ρ (K k)ᶜ).toReal := by
    intro k
    have hfi : Integrable f ρ := Integrable.of_bound (C := C) hf.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa using hC x)
    have hfχ : Integrable (fun x => f x * χ k x) ρ := Integrable.of_bound (C := C)
      (hf.mul (hχc k)).aestronglyMeasurable (ae_of_all _ fun x => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (hχI k x).1]
        calc |f x| * χ k x ≤ C * 1 := mul_le_mul (hC x) (hχI k x).2 (hχI k x).1 ((abs_nonneg _).trans (hC x))
          _ = C := mul_one C)
    rw [← integral_sub hfχ hfi]
    have hbd : Integrable (fun x => C * ((K k)ᶜ).indicator (fun _ => (1 : ℝ)) x) ρ :=
      ((integrable_const (μ := ρ) (1 : ℝ)).indicator (hKmeas k).compl).const_mul C
    refine (norm_integral_le_of_norm_le hbd (ae_of_all _ fun x => ?_)).trans ?_
    · by_cases hx : x ∈ K k
      · rw [hχ1 k hx]; simp [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hx)]
      · rw [Set.indicator_of_mem (Set.mem_compl hx)]
        have e : f x * χ k x - f x = -(f x * (1 - χ k x)) := by ring
        rw [e, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (by linarith [(hχI k x).2])]
        calc |f x| * (1 - χ k x) ≤ C * 1 :=
              mul_le_mul (hC x) (by linarith [(hχI k x).1]) (by linarith [(hχI k x).2])
                ((abs_nonneg _).trans (hC x))
          _ = C * 1 := rfl
          _ = C * 1 := rfl
    · rw [integral_const_mul, integral_indicator (hKmeas k).compl]
      simp [Measure.real]
  have hlim : Tendsto (fun k => C * (ρ (K k)ᶜ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcompl
    simpa using this.const_mul C
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

/-- Finite measures charging only `D` that agree on `C_c(D)` are equal. -/
theorem s113a_measure_eq_of_Cc {D : Set E} (hD : IsOpen D) {ν μ : Measure E} [IsFiniteMeasure ν]
    (hνD : ν Dᶜ = 0) (hμD : μ Dᶜ = 0)
    (hμint : ∀ ψ : E → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ D → Integrable ψ μ)
    (h : ∀ ψ : E → ℝ, Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ D →
      ∫ x, ψ x ∂ν = ∫ x, ψ x ∂μ) : ν = μ := by
  obtain ⟨K, χ, hKc, hKm, hKU, hχc, hχs, hχD, hχI, hχ1⟩ := s113a_exhaustion hD
  have hKmeas : ∀ k, MeasurableSet (K k) := fun k => (hKc k).isClosed.measurableSet
  -- μ is finite
  have hμK : ∀ k, μ (K k) ≤ ν Set.univ := by
    intro k
    have hint : Integrable (χ k) μ := hμint _ (hχc k) (hχs k) (hχD k)
    have hintν : Integrable (χ k) ν := (hχc k).integrable_of_hasCompactSupport (hχs k)
    calc μ (K k) = ∫⁻ x, (K k).indicator 1 x ∂μ := by
          rw [lintegral_indicator (hKmeas k)]; simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (χ k x) ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ K k
          · simp [Set.indicator_of_mem hx, hχ1 k hx]
          · simp [Set.indicator_of_notMem hx]
      _ = ENNReal.ofReal (∫ x, χ k x ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hχI k x).1)).symm
      _ = ENNReal.ofReal (∫ x, χ k x ∂ν) := by rw [h _ (hχc k) (hχs k) (hχD k)]
      _ = ∫⁻ x, ENNReal.ofReal (χ k x) ∂ν :=
          ofReal_integral_eq_lintegral_ofReal hintν (ae_of_all _ fun x => (hχI k x).1)
      _ ≤ ∫⁻ _, 1 ∂ν := lintegral_mono fun x => by simpa using (hχI k x).2
      _ = ν Set.univ := by simp
  have hμfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    have h1 : μ D ≤ ν Set.univ := by
      rw [← hKU]
      rw [hKm.measure_iUnion]
      exact iSup_le hμK
    have h2 : μ Set.univ ≤ μ D + μ Dᶜ := by
      calc μ Set.univ = μ (D ∪ Dᶜ) := by rw [Set.union_compl_self]
        _ ≤ μ D + μ Dᶜ := measure_union_le _ _
    rw [hμD, add_zero] at h2
    exact lt_of_le_of_lt (h2.trans h1) (measure_lt_top _ _)
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hC' : ∀ x, |f x| ≤ max C 0 := fun x => by
    rw [← Real.norm_eq_abs]; exact (hC x).trans (le_max_left _ _)
  have h1 := s113a_cutoff_tendsto hKc hKm hKU hχc hχI hχ1 hχs hνD f.continuous hC'
  have h2 := s113a_cutoff_tendsto hKc hKm hKU hχc hχI hχ1 hχs hμD f.continuous hC'
  have heq : ∀ k, ∫ x, f x * χ k x ∂ν = ∫ x, f x * χ k x ∂μ := fun k =>
    h _ (f.continuous.mul (hχc k)) ((hχs k).mul_left)
      ((tsupport_mul_subset_right).trans (hχD k))
  exact tendsto_nhds_unique (h1.congr heq) h2

end HRS.MS.S113X2

end
