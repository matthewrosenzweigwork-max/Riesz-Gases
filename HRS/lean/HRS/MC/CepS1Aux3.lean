import HRS.MC.CepS1Aux2

/-!
# Packet CEPS1 (auxiliary 3): barrier chain under a `C^{1,1}` potential

Mechanical copy-adaptation of theorems of `HRS/Stochastic/Particle.lean` (line ranges L3798-3882, L3891-3980, L3991-3999, L4337-4416) with
`Torus.IsCk 2 D.V` replaced by `cep_IsC11 D.V`; the hypothesis enters only through the Lipschitz
constant of `∇V` and the local Lipschitz continuity of the drift (`HRS.MC.CepC0.cepc0_locLipschitz`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS1

open HRS HRS.ClusterBarrier HRS.MC.CepC0

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem cluster_hitting_probability [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hM : Torus.SymNonpos D.M) (hV : cep_IsC11 D.V)
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → (Fin N → Euc d)} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) (hdk : D.invβ = 0 ∨ 2 ≤ d * (I.card - 1))
    (δ : ℝ) (hδ : 0 < δ) (q₁ : ℝ) (hq₁ : 0 < q₁) (T : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ≤
        ENNReal.ofReal (C / |Real.log a|) := by
  classical
  obtain ⟨q, C₀, hq, hqr, hC₀, hrem⟩ := clusterRemainder_bound D hK hV I hI δ hδ
  obtain ⟨C', hC'0, hC'⟩ := barrier_generator_bound D hM I hdk hI hq hqr hC₀
    {Z | ∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z}
    (fun Y hYS hYf hYq => hrem Y hYf hYq hYS)
  have hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C' :=
    fun Z hZS hZf => hC' Z hZS hZf
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set m : ℝ := Real.log (q / 2) with hm
  set Kb : ℝ := barrierPhi q (min q₁ (q / 2)) + m + C' * T' with hKb
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hKb0 : 0 ≤ Kb := by
    have h1 : -Real.log (q / 2) ≤ barrierPhi q (min q₁ (q / 2)) := barrierPhi_ge hq hmin0
    have := mul_nonneg hC'0 hT'0
    simp only [hKb, hm]; linarith
  refine ⟨min (q / 4) (min q₁ (Real.exp (-(2 * |m|)))), 2 * Kb, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min hq₁ (Real.exp_pos _))
  intro a ha hlt
  have haq : a < q / 4 := lt_of_lt_of_le hlt (min_le_left _ _)
  have haq₁ : a < q₁ := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < Real.exp (-(2 * |m|)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : Real.log a < -(2 * |m|) := by
    rw [Real.log_lt_iff_lt_exp ha]; exact hae
  have hlogneg : Real.log a < 0 := by have := abs_nonneg m; linarith
  have habs : |Real.log a| = -Real.log a := abs_of_neg hlogneg
  have hΦa : barrierPhi q a = -Real.log a := barrierPhi_of_le hq haq.le
  have hca : |Real.log a| / 2 ≤ barrierPhi q a + m := by
    rw [hΦa, habs]
    have := neg_abs_le m
    have := le_abs_self m
    linarith
  have hca0 : 0 < barrierPhi q a + m := lt_of_lt_of_le (by rw [habs]; linarith) hca
  -- level estimates
  have hB : ∀ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T' ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T' := fun n =>
    barrier_level_estimate D hK hV hW' hsol I hI hq hC'0 hgen hT'0 ha hq₁ n
  choose B hBm hBsub hBest using hB
  have hPB : ∀ n, P (B n) ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
    intro n
    have h1 : (P (B n)).toReal ≤ 2 * Kb / |Real.log a| := by
      have hlogpos : 0 < |Real.log a| := by rw [habs]; linarith
      rw [le_div_iff₀ hlogpos]
      have h2 := hBest n
      have h3 : (P (B n)).toReal * (|Real.log a| / 2) ≤
          (P (B n)).toReal * (barrierPhi q a + m) :=
        mul_le_mul_of_nonneg_left hca ENNReal.toReal_nonneg
      nlinarith
    calc P (B n) = ENNReal.ofReal (P (B n)).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  -- the event is contained in the liminf
  have hsub : {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ⊆
      ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    rintro ω ⟨hq0, t, ht0, htT, htτ, hQt, hδt⟩
    have hY0 : Y 0 ω = Y₀ ω := hsol.sol.init ω
    obtain ⟨n₀, hn₀⟩ := reach_eventually (τ := τ ω) (y := fun t => Y t ω) I (δ := δ) (q₁ := q₁)
      (T := T') haq₁.le (hsol.sol.cont ω) (hsol.mem ω) (by simpa [hY0] using hq0)
      ⟨t, ht0, htT.trans (le_max_left _ _), htτ, hQt, hδt⟩
    refine Set.mem_iUnion.2 ⟨n₀, Set.mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨hK0, r, hr0, hrT, hhit, hQr⟩ := hn₀ n hn
    exact hBsub n ω (by simpa [hY0] using hK0) hq0 ⟨r, hr0, hrT, hhit, hQr⟩
  have hmono : Monotone fun n₀ : ℕ => ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    intro k l hkl
    exact Set.iInter₂_mono' fun n hn => ⟨n, hkl.trans hn, subset_rfl⟩
  calc P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω}
      ≤ P (⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := measure_mono hsub
    _ = ⨆ n₀ : ℕ, P (⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
        refine iSup_le fun n₀ => ?_
        exact (measure_mono (Set.iInter₂_subset n₀ le_rfl)).trans (hPB n₀)

theorem cluster_barrier_of_hdk [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hM : Torus.SymNonpos D.M) (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hdk : D.invβ = 0 ∨ 2 ≤ d * (I.card - 1))
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  classical
  set F : ℝ → Set Ω := fun δ => {ω | ∃ s : ℝ, 0 ≤ s ∧ s < T ∧ (s : WithTop ℝ) < τ ω ∧
    ∃ j, j ∉ I ∧ clusterDispersionLift (insert j I) (Y s ω) ≤ δ} with hF
  set X : ℕ → Set Ω := fun k => {ω | ClusterCollapse I T τ Y ω ∧
    1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω)} with hX
  -- Step A
  have hA : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → P (X k ∩ (F δ)ᶜ) = 0 := by
    intro k δ hδ
    obtain ⟨a₀, C, ha₀, hC⟩ := cluster_hitting_probability D hK hM hV hW' hsol I hI hdk δ hδ
      (1 / ((k : ℝ) + 1)) (by positivity) T
    have hsub : ∀ a : ℝ, 0 < a → X k ∩ (F δ)ᶜ ⊆
        {ω | 1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} := by
      intro a ha ω ⟨⟨hcol, hq0⟩, hnF⟩
      refine ⟨hq0, ?_⟩
      obtain ⟨t, ht0, htT, htτ, hQt⟩ := hcol a ha
      refine ⟨t, ht0, htT.le, htτ, hQt.le, fun s hs0 hst j hj => ?_⟩
      by_contra hle
      push_neg at hle
      exact hnF ⟨s, hs0, lt_of_le_of_lt hst htT,
        lt_of_le_of_lt (by exact_mod_cast hst) htτ, j, hj, hle⟩
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-Real.log a₀)
    have hev : ∀ n : ℕ, n₀ ≤ n → P (X k ∩ (F δ)ᶜ) ≤ ENNReal.ofReal (C / (n : ℝ)) := by
      intro n hn
      have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      have hlt : Real.exp (-(n : ℝ)) < a₀ := by
        rw [← Real.lt_log_iff_exp_lt ha₀]; linarith
      have := hC _ (Real.exp_pos _) hlt
      rw [Real.log_exp, abs_neg, Nat.abs_cast] at this
      exact (measure_mono (hsub _ (Real.exp_pos _))).trans this
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (C / (n : ℝ))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C)
      simpa using this
    exact le_antisymm (ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨n₀, hev⟩)) bot_le
  -- Step B
  have hB : ∀ k : ℕ, X k ⊆ (⋃ j ∈ ({j | j ∉ I} : Set (Fin N)),
        {ω | ClusterCollapse (insert j I) T τ Y ω}) ∪ ⋃ l : ℕ, X k ∩ (F (1 / ((l : ℝ) + 1)))ᶜ := by
    intro k ω hω
    by_cases hcol : ω ∈ ⋃ j ∈ ({j | j ∉ I} : Set (Fin N)), {ω | ClusterCollapse (insert j I) T τ Y ω}
    · exact Or.inl hcol
    right
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcol
    have hnc : ∀ j, ∃ ε : ℝ, 0 < ε ∧ (j ∉ I → ∀ t : ℝ, 0 ≤ t → t < T → (t : WithTop ℝ) < τ ω →
        ε ≤ clusterDispersionLift (insert j I) (Y t ω)) := by
      intro j
      by_cases hj : j ∈ I
      · exact ⟨1, one_pos, fun h => absurd hj h⟩
      · have := hcol j hj
        unfold ClusterCollapse at this
        push_neg at this
        obtain ⟨ε, hε, h⟩ := this
        exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
    choose ε hε0 hε using hnc
    set ε₀ : ℝ := (1 + ∑ j, 1 / ε j)⁻¹ with hε₀
    have hS : 0 ≤ ∑ j, 1 / ε j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hε0 j)).le
    have hε₀pos : 0 < ε₀ := inv_pos.2 (by linarith)
    have hε₀le : ∀ j, ε₀ ≤ ε j := by
      intro j
      have h1 : 1 / ε j ≤ ∑ j, 1 / ε j :=
        Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.2 (hε0 j)).le)
          (Finset.mem_univ j)
      rw [hε₀]
      have : (1 + ∑ j, 1 / ε j)⁻¹ ≤ (1 / ε j)⁻¹ := inv_anti₀ (one_div_pos.2 (hε0 j)) (by linarith)
      simpa using this
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε₀pos
    refine Set.mem_iUnion.2 ⟨l, hω, ?_⟩
    rintro ⟨s, hs0, hsT, hsτ, j, hj, hle⟩
    have := hε j hj s hs0 hsT hsτ
    linarith [hε₀le j]
  -- conclusion
  have hk : {ω | ClusterCollapse I T τ Y ω} ⊆ ⋃ k : ℕ, X k := by
    intro ω hω
    have hfree : Y₀ ω ∈ liftedFree d N := by
      have := hsol.mem ω 0 le_rfl (by simpa using hsol.pos ω)
      rwa [hsol.sol.init ω] at this
    have hpos := clusterDispersionLift_pos hI hfree
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨k, hω, hk.le⟩
  refine measure_mono_null hk (measure_iUnion_null fun k => ?_)
  refine measure_mono_null (hB k) (measure_union_null ?_ (measure_iUnion_null fun l => ?_))
  · refine measure_biUnion_null_iff (Set.to_countable _) |>.2 fun j hj => ?_
    exact hind (insert j I) (Finset.ssubset_insert hj) (Finset.card_insert_of_notMem hj) T
  · exact hA k _ (by positivity)

theorem cluster_barrier [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hM : Torus.SymNonpos D.M) (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hdk : 2 ≤ d * (I.card - 1))
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  exact cluster_barrier_of_hdk D hK hM hV hW' hsol I hI (Or.inr hdk) hind T

theorem cluster_hitting_of_gen [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hV : cep_IsC11 D.V)
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → (Fin N → Euc d)} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) {q C' : ℝ} (hq : 0 < q) (hC'0 : 0 ≤ C')
    (δ : ℝ) (hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C')
    (q₁ : ℝ) (hq₁ : 0 < q₁) (T : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ≤
        ENNReal.ofReal (C / |Real.log a|) := by
  classical
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set m : ℝ := Real.log (q / 2) with hm
  set Kb : ℝ := barrierPhi q (min q₁ (q / 2)) + m + C' * T' with hKb
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hKb0 : 0 ≤ Kb := by
    have h1 : -Real.log (q / 2) ≤ barrierPhi q (min q₁ (q / 2)) := barrierPhi_ge hq hmin0
    have := mul_nonneg hC'0 hT'0
    simp only [hKb, hm]; linarith
  refine ⟨min (q / 4) (min q₁ (Real.exp (-(2 * |m|)))), 2 * Kb, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min hq₁ (Real.exp_pos _))
  intro a ha hlt
  have haq : a < q / 4 := lt_of_lt_of_le hlt (min_le_left _ _)
  have haq₁ : a < q₁ := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < Real.exp (-(2 * |m|)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : Real.log a < -(2 * |m|) := by
    rw [Real.log_lt_iff_lt_exp ha]; exact hae
  have hlogneg : Real.log a < 0 := by have := abs_nonneg m; linarith
  have habs : |Real.log a| = -Real.log a := abs_of_neg hlogneg
  have hΦa : barrierPhi q a = -Real.log a := barrierPhi_of_le hq haq.le
  have hca : |Real.log a| / 2 ≤ barrierPhi q a + m := by
    rw [hΦa, habs]
    have := neg_abs_le m
    have := le_abs_self m
    linarith
  have hca0 : 0 < barrierPhi q a + m := lt_of_lt_of_le (by rw [habs]; linarith) hca
  -- level estimates
  have hB : ∀ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T' ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T' := fun n =>
    barrier_level_estimate D hK hV hW' hsol I hI hq hC'0 hgen hT'0 ha hq₁ n
  choose B hBm hBsub hBest using hB
  have hPB : ∀ n, P (B n) ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
    intro n
    have h1 : (P (B n)).toReal ≤ 2 * Kb / |Real.log a| := by
      have hlogpos : 0 < |Real.log a| := by rw [habs]; linarith
      rw [le_div_iff₀ hlogpos]
      have h2 := hBest n
      have h3 : (P (B n)).toReal * (|Real.log a| / 2) ≤
          (P (B n)).toReal * (barrierPhi q a + m) :=
        mul_le_mul_of_nonneg_left hca ENNReal.toReal_nonneg
      nlinarith
    calc P (B n) = ENNReal.ofReal (P (B n)).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  -- the event is contained in the liminf
  have hsub : {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ⊆
      ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    rintro ω ⟨hq0, t, ht0, htT, htτ, hQt, hδt⟩
    have hY0 : Y 0 ω = Y₀ ω := hsol.sol.init ω
    obtain ⟨n₀, hn₀⟩ := reach_eventually (τ := τ ω) (y := fun t => Y t ω) I (δ := δ) (q₁ := q₁)
      (T := T') haq₁.le (hsol.sol.cont ω) (hsol.mem ω) (by simpa [hY0] using hq0)
      ⟨t, ht0, htT.trans (le_max_left _ _), htτ, hQt, hδt⟩
    refine Set.mem_iUnion.2 ⟨n₀, Set.mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨hK0, r, hr0, hrT, hhit, hQr⟩ := hn₀ n hn
    exact hBsub n ω (by simpa [hY0] using hK0) hq0 ⟨r, hr0, hrT, hhit, hQr⟩
  have hmono : Monotone fun n₀ : ℕ => ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    intro k l hkl
    exact Set.iInter₂_mono' fun n hn => ⟨n, hkl.trans hn, subset_rfl⟩
  calc P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω}
      ≤ P (⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := measure_mono hsub
    _ = ⨆ n₀ : ℕ, P (⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
        refine iSup_le fun n₀ => ?_
        exact (measure_mono (Set.iInter₂_subset n₀ le_rfl)).trans (hPB n₀)

end HRS.MC.CepS1
