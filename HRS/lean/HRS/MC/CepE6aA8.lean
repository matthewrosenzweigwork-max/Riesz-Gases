import HRS.MC.CepE6aA7

/-!
# Packet CEPE6A, file 8: the main theorem `cep_E6_abcd` (conjuncts (a)-(d) of `cep_E6_limit_solution`)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_E6_abcd_ext [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) :
    ∃ Zl : ℝ → Ω → Ch N, (∀ ω, Continuous fun t => Zl t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧
      (∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T)) ∧
      (∀ T : ℝ, ∃ C : ℝ, ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T,
          ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|)) ∂P ≤ ENNReal.ofReal C) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ∑ k : Fin N, ∑ l : Fin N,
          (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else 0)) (Set.Icc 0 T)) := by
  classical
  have hℱ := hW'.complete
  -- the Cauchy property of the shifted sequence
  have hcau : ∀ T ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ ≤ m → n₀ ≤ n →
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z (m + 1) t ω - Z (n + 1) t ω‖} < ENNReal.ofReal ε := by
    intro T ε hε
    obtain ⟨n₀, h⟩ := HRS.MC.CepE5c.cep_E5c_cauchy_proof hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ T ε hε
    exact ⟨n₀, fun m n hm hn => h (m + 1) (n + 1) (by omega) (by omega)⟩
  obtain ⟨k, hkmono, hk2, hkj, Zl, G, hZlc, hZlm, hGm, hG0, hunif, hprob⟩ :=
    e6a_limit_exists hℱ (Z := fun n => Z (n + 1)) (fun n ω => (hZ (n + 1) (by omega)).1 ω)
      (fun n t ht => (hZ (n + 1) (by omega)).2.1 t ht) hcau (fun j => 2 ^ j)
  set K : ℕ → ℕ := fun j => k j + 1 with hK
  have hK1 : ∀ j, 1 ≤ K j := fun j => by simp [hK]
  have hK2 : ∀ j, 2 ^ j ≤ K j := fun j => by have := hk2 j; simp only [hK]; omega
  have hKpos : ∀ j, (0 : ℝ) < (K j : ℝ) := fun j => by exact_mod_cast hK1 j
  -- the constants of E4
  choose C hC using fun T : ℕ =>
    e6a_E4_lint hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ (T : ℝ) (Nat.cast_nonneg T)
  -- measurability
  have hZj : ∀ n, 1 ≤ n → Measurable fun p : Ω × ℝ => Z n (max p.2 0) p.1 := fun n hn =>
    (e6a_joint (hZ n hn).1 (hZ n hn).2.1).comp measurable_swap
  have hZlj : Measurable fun p : Ω × ℝ => Zl (max p.2 0) p.1 :=
    (e6a_joint hZlc hZlm).comp measurable_swap
  -- the resolvent values
  let Wf : ℕ → Ω × ℝ → Ch N := fun j p => J (K j) (Z (K j) (max p.2 0) p.1)
  have hWm : ∀ j, Measurable (Wf j) := fun j =>
    (e6a_J_cont hJ (hKpos j)).measurable.comp (hZj (K j) (hK1 j))
  have hWa : ∀ j p, Wf j p ∈ cep_Alcove N := fun j p => hJ.mem _ _ (hKpos j)
  let Uf : ℕ → Ω × ℝ → ℝ≥0∞ := fun j p => ENNReal.ofReal ‖Z (K j) (max p.2 0) p.1 - Wf j p‖
  have hUm : ∀ j, Measurable (Uf j) := fun j =>
    ENNReal.measurable_ofReal.comp (((hZj (K j) (hK1 j)).sub (hWm j)).norm)
  let Ef : ℕ → Ω × ℝ → ℝ≥0∞ := fun j p =>
    ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Wf j p)) i|)
  have hEm : ∀ j, Measurable (Ef j) := fun j =>
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ =>
      ((EuclideanSpace.proj i).continuous.measurable.comp ((e6a_gradient_measurable a).comp (hWm j))).abs)
  -- the force identity
  have hforce : ∀ j (z : Ch N), gradient (cep_chamberPot a N) (J (K j) z) = (K j : ℝ) • (z - J (K j) z) :=
    fun j z => (hJ.force _ _ (hKpos j)).symm
  -- bound on the force integral
  have hE : ∀ (T : ℕ) (j : ℕ),
      ∫⁻ p, Ef j p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))) ≤ ENNReal.ofReal (C T) := by
    intro T j
    rw [lintegral_prod _ (hEm j).aemeasurable]
    refine le_trans (le_of_eq ?_) (hC T (K j) (hK1 j))
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
    simp only [Ef, Wf, max_eq_left hs.1, hforce]
  -- bound on the distance integral
  have hU : ∀ (T : ℕ) (j : ℕ),
      ∫⁻ p, Uf j p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))) ≤ ENNReal.ofReal (C T) * (2⁻¹ : ℝ≥0∞) ^ j := by
    intro T j
    have hpt : ∀ p, Uf j p ≤ ENNReal.ofReal (1 / (K j : ℝ)) * Ef j p := by
      intro p
      simp only [Uf, Ef]
      rw [← ENNReal.ofReal_mul (by have := hKpos j; positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set z := Z (K j) (max p.2 0) p.1 with hz
      have h1 : z - J (K j) z = (1 / (K j : ℝ)) • (gradient (cep_chamberPot a N) (J (K j) z)) := by
        rw [hforce, smul_smul, one_div, inv_mul_cancel₀ (hKpos j).ne', one_smul]
      show ‖z - J (K j) z‖ ≤ _
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by have := hKpos j; positivity)]
      exact mul_le_mul_of_nonneg_left (e6a_norm_le_sum _) (by have := hKpos j; positivity)
    calc ∫⁻ p, Uf j p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T)))
        ≤ ∫⁻ p, ENNReal.ofReal (1 / (K j : ℝ)) * Ef j p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (1 / (K j : ℝ)) * ∫⁻ p, Ef j p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))) :=
          lintegral_const_mul _ (hEm j)
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ j * ENNReal.ofReal (C T) := by
          refine mul_le_mul ?_ (hE T j) (by positivity) (by positivity)
          have h2 : (1 : ℝ) / (K j : ℝ) ≤ (1 / 2 : ℝ) ^ j := by
            rw [one_div_pow, one_div_le_one_div (hKpos j) (by positivity)]
            exact_mod_cast hK2 j
          refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_pow (by norm_num)]
          congr 1
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
      _ = ENNReal.ofReal (C T) * (2⁻¹ : ℝ≥0∞) ^ j := mul_comm _ _
  have hsmall : ∀ T : ℕ, ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))),
      Tendsto (fun j => Uf j p) atTop (𝓝 0) := fun T =>
    e6a_ae_tendsto_zero hUm ENNReal.ofReal_ne_top (hU T)
  -- pathwise convergence of the resolvent values
  have hWconv : ∀ ω ∈ G, ∀ (T : ℕ) (s : ℝ), s ∈ Icc (0 : ℝ) T →
      Tendsto (fun j => Uf j (ω, s)) atTop (𝓝 0) → Tendsto (fun j => Wf j (ω, s)) atTop (𝓝 (Zl s ω)) := by
    intro ω hω T s hs hU0
    have hY : Tendsto (fun j => Z (K j) s ω) atTop (𝓝 (Zl s ω)) :=
      (hunif ω hω T).tendsto_at hs
    have hd : Tendsto (fun j => ‖Z (K j) s ω - Wf j (ω, s)‖) atTop (𝓝 0) := by
      have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hU0
      simp only [Function.comp_def, ENNReal.toReal_zero] at h1
      refine h1.congr fun j => ?_
      simp only [Uf, max_eq_left hs.1]
      rw [ENNReal.toReal_ofReal (norm_nonneg _)]
    have h2 : Tendsto (fun j => Z (K j) s ω - Wf j (ω, s)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.2 hd
    have h3 := hY.sub h2
    simp only [sub_zero] at h3
    refine h3.congr fun j => ?_
    simp
  -- the Fatou step
  have hF : ∀ T : ℕ, ∫⁻ p, e6a_ext a N (Zl (max p.2 0) p.1) ∂(P.prod (volume.restrict (Icc (0 : ℝ) T)))
      ≤ ENNReal.ofReal (C T) := by
    intro T
    refine e6a_fatou ha (Zl := fun p : Ω × ℝ => Zl (max p.2 0) p.1) hZlj hWm hWa (hE T) ?_
    have hG' : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))), p.1 ∈ G := by
      refine (Measure.quasiMeasurePreserving_fst (μ := P) (ν := volume.restrict (Icc (0 : ℝ) T))).ae ?_
      rw [ae_iff]; exact hG0
    have hS' : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T))), p.2 ∈ Icc (0 : ℝ) T :=
      (Measure.quasiMeasurePreserving_snd (μ := P) (ν := volume.restrict (Icc (0 : ℝ) T))).ae
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hG', hS', hsmall T] with p hpG hpS hpU
    have := hWconv p.1 hpG T p.2 hpS hpU
    simpa [max_eq_left hpS.1] using this
  -- the iterated form
  let Ie : ℕ → Ω → ℝ≥0∞ := fun T ω => ∫⁻ s in Icc (0 : ℝ) T, e6a_ext a N (Zl s ω)
  have hextm : ∀ ω, Measurable fun s => e6a_ext a N (Zl s ω) := fun ω =>
    (e6a_measurable_ext a).comp (hZlc ω).measurable
  have hextj : Measurable fun p : Ω × ℝ => e6a_ext a N (Zl (max p.2 0) p.1) :=
    (e6a_measurable_ext a).comp hZlj
  have hIeq : ∀ T : ℕ, Ie T = fun ω => ∫⁻ s, e6a_ext a N (Zl (max s 0) ω)
      ∂(volume.restrict (Icc (0 : ℝ) T)) := by
    intro T; funext ω
    exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp [max_eq_left hs.1])
  have hIe : ∀ T : ℕ, ∫⁻ ω, Ie T ω ∂P ≤ ENNReal.ofReal (C T) := by
    intro T
    refine le_trans (le_of_eq ?_) (hF T)
    rw [lintegral_prod _ hextj.aemeasurable, hIeq T]
  have hIem : ∀ T : ℕ, Measurable (Ie T) := by
    intro T; rw [hIeq T]
    exact Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ => e6a_ext a N (Zl (max p.2 0) p.1)) hextj
  have hIefin : ∀ᵐ ω ∂P, ∀ T : ℕ, Ie T ω < ⊤ := by
    rw [ae_all_iff]; intro T
    exact ae_lt_top (hIem T) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hIe T))
  have hae_G : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have hsm_ae : ∀ᵐ ω ∂P, ∀ T : ℕ, ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun j => Uf j (ω, s)) atTop (𝓝 0) := by
    rw [ae_all_iff]; intro T
    exact e6a_ae_ae_of_ae_prod (hsmall T)
  have hnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0 := by
    filter_upwards [hIefin] with ω hω T
    have hfin : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) ⌈T⌉₊)), e6a_ext a N (Zl s ω) < ⊤ :=
      ae_lt_top (hextm ω) (hω ⌈T⌉₊).ne
    rw [ae_restrict_iff' measurableSet_Icc, ae_iff] at hfin
    refine measure_mono_null ?_ hfin
    rintro s ⟨hs, hna⟩ h
    have := h ⟨hs.1, hs.2.trans (Nat.le_ceil T)⟩
    rw [e6a_ext_eq_top hna] at this
    exact lt_irrefl _ this
  refine ⟨Zl, hZlc, hZlm, ?_, ?_, hnull, ?_, ?_, ?_⟩
  · intro T ε hε
    exact (tendsto_add_atTop_iff_nat (f := fun n => P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) 1).1
      (hprob T ε hε)
  · filter_upwards [hae_G, hsm_ae] with ω hωG hω t ht
    have hT0 : (0 : ℝ) < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by positivity
    have hclosed : IsClosed {s : ℝ | Zl s ω ∈ closure (cep_Alcove N)} :=
      isClosed_closure.preimage (hZlc ω)
    have hae : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) ((⌈t⌉₊ + 1 : ℕ) : ℝ))),
        s ∈ {s : ℝ | Zl s ω ∈ closure (cep_Alcove N)} := by
      filter_upwards [hω (⌈t⌉₊ + 1), ae_restrict_mem measurableSet_Icc] with s hs1 hs2
      have := hWconv ω hωG (⌈t⌉₊ + 1) s hs2 hs1
      exact mem_closure_of_tendsto this (Eventually.of_forall fun j => hWa j (ω, s))
    have hsub := e6a_Icc_subset_of_ae hclosed hT0 hae
    refine hsub ⟨ht, ?_⟩
    have := Nat.le_ceil t
    push_cast
    linarith
  · filter_upwards [hIefin] with ω hω T
    have hint : IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Icc (0 : ℝ) ⌈T⌉₊) := by
      refine ⟨(((e6a_gradient_measurable a).comp (hZlc ω).measurable).norm).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      calc ∫⁻ s in Icc (0 : ℝ) ⌈T⌉₊, ‖‖gradient (cep_chamberPot a N) (Zl s ω)‖‖ₑ
          ≤ ∫⁻ s in Icc (0 : ℝ) ⌈T⌉₊, e6a_ext a N (Zl s ω) := by
            refine lintegral_mono fun s => ?_
            rw [enorm_norm, ← ofReal_norm]
            exact e6a_ofReal_norm_le_ext a _
        _ < ⊤ := hω ⌈T⌉₊
    exact hint.mono_set (Icc_subset_Icc_right (Nat.le_ceil T))
  · intro T
    refine ⟨C ⌈T⌉₊, ?_⟩
    calc ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T,
          ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|)) ∂P
        ≤ ∫⁻ ω, Ie ⌈T⌉₊ ω ∂P := by
          refine lintegral_mono fun ω => ?_
          calc ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|)
              ≤ ∫⁻ s in Icc (0 : ℝ) ⌈T⌉₊, ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|) :=
                lintegral_mono_set (Icc_subset_Icc_right (Nat.le_ceil T))
            _ ≤ Ie ⌈T⌉₊ ω := lintegral_mono fun s => e6a_ofReal_l1_le_ext a _
      _ ≤ ENNReal.ofReal (C ⌈T⌉₊) := hIe _
  · obtain ⟨c1, c2, hc1, hc2, hcb⟩ := e6a_pair_inv_le ha N
    filter_upwards [hIefin, hnull] with ω hω hn T
    have hl1m : Measurable fun s : ℝ => ∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i| :=
      Finset.measurable_sum _ fun i _ =>
        ((EuclideanSpace.proj i).continuous.measurable.comp
          ((e6a_gradient_measurable a).comp (hZlc ω).measurable)).abs
    have hl1 : Integrable (fun s : ℝ => ∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|)
        (volume.restrict (Icc (0 : ℝ) ⌈T⌉₊)) := by
      refine ⟨hl1m.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s => Finset.sum_nonneg fun i _ => abs_nonneg _)]
      calc ∫⁻ s in Icc (0 : ℝ) ⌈T⌉₊, ENNReal.ofReal (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|)
          ≤ ∫⁻ s in Icc (0 : ℝ) ⌈T⌉₊, e6a_ext a N (Zl s ω) := lintegral_mono fun s => e6a_ofReal_l1_le_ext a _
        _ < ⊤ := hω ⌈T⌉₊
    have hbound : Integrable (fun s : ℝ => c1 * (∑ i, |(gradient (cep_chamberPot a N) (Zl s ω)) i|) + c2)
        (volume.restrict (Icc (0 : ℝ) ⌈T⌉₊)) :=
      (hl1.const_mul c1).add (integrable_const c2)
    have hpm : Measurable fun s : ℝ => ∑ k : Fin N, ∑ l : Fin N,
        (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else 0) := by
      refine Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
      by_cases hkl : k < l
      · simp only [hkl, if_true]
        have hd : Measurable fun s : ℝ => Zl s ω l - Zl s ω k :=
          ((EuclideanSpace.proj l).continuous.measurable.comp (hZlc ω).measurable).sub
            ((EuclideanSpace.proj k).continuous.measurable.comp (hZlc ω).measurable)
        exact measurable_const.div (hd.min (measurable_const.sub hd))
      · simp only [hkl, ite_false]; exact measurable_const
    have hint : IntegrableOn (fun s : ℝ => ∑ k : Fin N, ∑ l : Fin N,
        (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else 0))
        (Icc (0 : ℝ) ⌈T⌉₊) := by
      refine Integrable.mono' hbound hpm.aestronglyMeasurable ?_
      have halc : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) ⌈T⌉₊)), Zl s ω ∈ cep_Alcove N := by
        rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
        refine measure_mono_null ?_ (hn ⌈T⌉₊)
        rintro s hs
        simp only [mem_setOf_eq, not_imp] at hs
        exact hs
      filter_upwards [halc] with s hs
      have hnn : 0 ≤ ∑ k : Fin N, ∑ l : Fin N,
          (if k < l then 1 / min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) else (0 : ℝ)) := by
        refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
        by_cases hkl : k < l
        · simp only [hkl, if_true]
          have h1 := hs.1 k l hkl
          have h2 := hs.2 k l
          have : 0 < min (Zl s ω l - Zl s ω k) (1 - (Zl s ω l - Zl s ω k)) := lt_min (by linarith) (by linarith)
          positivity
        · simp [hkl]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hcb _ hs
    exact hint.mono_set (Icc_subset_Icc_right (Nat.le_ceil T))

/-- **Conjuncts (a)-(d) of `cep_E6_limit_solution`** (everything except the final integral equation). -/
theorem cep_E6_abcd [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) :
    ∃ Zl : ℝ → Ω → Ch N, (∀ ω, Continuous fun t => Zl t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧
      (∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T)) := by
  obtain ⟨Zl, h1, h2, h3, h4, h5, h6, -, -⟩ := cep_E6_abcd_ext hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ
  exact ⟨Zl, h1, h2, h3, h4, h5, h6⟩

end HRS.MC.CepE6A
