import HRS.Uniform.Q45Cov8

/-!
# Q45 (Lemma 3.20): the covariance formula for stochastic convolutions
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Formula

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma mesh_small {t2 : ℝ} {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, t2 / ((N : ℝ) + 1) < δ := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (t2 / δ)
  filter_upwards [eventually_ge_atTop N0] with N hN
  have hN' : (N0 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hN0
  nlinarith

theorem cov_formula_le {S : EvolData H E} {T K : ℝ} (hT : 0 ≤ T) (hS : S.MaxHyp T K)
    {G : ℝ → Ω → H} {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hDb : IsDetCovDensity T Db)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => if r ≤ T then Db r else 0))
    {Z : ℝ → Ω → E} (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    {t1 t2 : ℝ} (h1 : t1 ∈ Set.Icc (0 : ℝ) T) (h2 : t2 ∈ Set.Icc (0 : ℝ) T) (h12 : t1 ≤ t2)
    (ℓ1 ℓ2 : E →L[ℝ] ℝ) :
    ∫ ω, ℓ1 (Z t1 ω) * ℓ2 (Z t2 ω) ∂P =
      ∫ r in Set.Icc 0 t1, Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2) := by
  have hev := hS.1
  set Dd : ℝ → H →L[ℝ] H →L[ℝ] ℝ := fun r => if r ≤ T then Db r else 0 with hDd
  have hG' : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Dd r) := hG
  -- the partitions
  have hpmono : ∀ N : ℕ, Monotone (part t1 t2 (N + 1)) := fun N => part_mono h1.1 h12 (N + 1)
  have hp0 : ∀ N : ℕ, 0 ≤ part t1 t2 (N + 1) 0 := fun N => (part_zero t1 t2 (N + 1)).ge
  have hpT : ∀ N i, i ≤ 2 * (N + 1) → part t1 t2 (N + 1) i ≤ T := fun N i hi =>
    (part_le h1.1 h12 (Nat.succ_pos N) hi).trans h2.2
  -- Riemann sums and their functionals
  set R1 : ℕ → Ω → E := fun N ω =>
    riemannSum S.VE S.j G t1 (fun i : Fin (N + 1 + 1) => part t1 t2 (N + 1) i) ω with hR1
  set R2 : ℕ → Ω → E := fun N ω =>
    riemannSum S.VE S.j G t2 (fun i : Fin (2 * (N + 1) + 1) => part t1 t2 (N + 1) i) ω with hR2
  set X : ℕ → Ω → ℝ := fun N ω => ℓ1 (R1 N ω) with hX
  set Y : ℕ → Ω → ℝ := fun N ω => ℓ2 (R2 N ω) with hY
  set u1 : ℕ → ℕ → H := fun N i => pullbackVec S t1 (part t1 t2 (N + 1) i) ℓ1 with hu1
  set u2 : ℕ → ℕ → H := fun N i => pullbackVec S t2 (part t1 t2 (N + 1) i) ℓ2 with hu2
  have hXe : ∀ N ω, X N ω = ∑ i ∈ Finset.range (N + 1), incr G (part t1 t2 (N + 1)) (u1 N) i ω := by
    intro N ω
    exact functional_riemannSum S G t1 ℓ1 (part t1 t2 (N + 1)) (N + 1) ω
  have hYe : ∀ N ω, Y N ω = ∑ k ∈ Finset.range (2 * (N + 1)), incr G (part t1 t2 (N + 1)) (u2 N) k ω := by
    intro N ω
    exact functional_riemannSum S G t2 ℓ2 (part t1 t2 (N + 1)) (2 * (N + 1)) ω
  have hXmem : ∀ N, MemLp (X N) 2 P := by
    intro N
    have : X N = fun ω => ∑ i ∈ Finset.range (N + 1), incr G (part t1 t2 (N + 1)) (u1 N) i ω :=
      funext (hXe N)
    rw [this]
    refine memLp_finsetSum _ fun i hi => ?_
    exact incr_memLp hG' (hpmono N) (hp0 N) (hpT N (i + 1) (by
      have := Finset.mem_range.1 hi; omega)) _
  have hYmem : ∀ N, MemLp (Y N) 2 P := by
    intro N
    have : Y N = fun ω => ∑ k ∈ Finset.range (2 * (N + 1)), incr G (part t1 t2 (N + 1)) (u2 N) k ω :=
      funext (hYe N)
    rw [this]
    refine memLp_finsetSum _ fun k hk => ?_
    exact incr_memLp hG' (hpmono N) (hp0 N) (hpT N (k + 1) (by
      have := Finset.mem_range.1 hk; omega)) _
  -- convergence of the functionals in `L²`
  have hmeshT : ∀ (n : ℕ → ℕ) (hn : ∀ N, n N ≤ 2 * (N + 1)), ∀ δ > 0, ∀ᶠ N in atTop,
      ∀ i : Fin (n N), part t1 t2 (N + 1) ((i.succ : Fin (n N + 1)) : ℕ) -
        part t1 t2 (N + 1) ((i.castSucc : Fin (n N + 1)) : ℕ) < δ := by
    intro n hn δ hδ
    filter_upwards [mesh_small (t2 := t2) hδ] with N hN i
    simp only [Fin.val_succ, Fin.val_castSucc]
    have := part_step h1.1 h12 (Nat.succ_pos N) i
    have e : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [e] at this
    exact lt_of_le_of_lt this hN
  have hmonoFin : ∀ (N n : ℕ), Monotone (fun i : Fin (n + 1) => part t1 t2 (N + 1) i) :=
    fun N n i j hij => hpmono N (Fin.le_def.1 hij)
  have hconv1 : Tendsto (fun N => ∫⁻ ω, ‖X N ω - ℓ1 (Z t1 ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    refine functional_tendsto (hZ t1 h1) ℓ1 (fun N => N + 1)
      (fun N => fun i : Fin (N + 1 + 1) => part t1 t2 (N + 1) i) (fun N => ?_) (fun N => ?_)
      (fun N => hmonoFin N _) ?_
    · simp [part_zero]
    · simp [part_M (Nat.succ_pos N)]
    · intro δ hδ
      exact hmeshT (fun N => N + 1) (fun N => by omega) δ hδ
  have hconv2 : Tendsto (fun N => ∫⁻ ω, ‖Y N ω - ℓ2 (Z t2 ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    refine functional_tendsto (hZ t2 h2) ℓ2 (fun N => 2 * (N + 1))
      (fun N => fun i : Fin (2 * (N + 1) + 1) => part t1 t2 (N + 1) i) (fun N => ?_) (fun N => ?_)
      (fun N => hmonoFin N _) ?_
    · simp [part_zero]
    · simp [part_2M (Nat.succ_pos N)]
    · intro δ hδ
      exact hmeshT (fun N => 2 * (N + 1)) (fun N => le_rfl) δ hδ
  have ha1m : AEStronglyMeasurable (fun ω => ℓ1 (Z t1 ω)) P :=
    (ℓ1.continuous.measurable.comp_aemeasurable (hZm t1 h1)).aestronglyMeasurable
  have hb2m : AEStronglyMeasurable (fun ω => ℓ2 (Z t2 ω)) P :=
    (ℓ2.continuous.measurable.comp_aemeasurable (hZm t2 h2)).aestronglyMeasurable
  have hL1 : Tendsto (fun N => eLpNorm (X N - fun ω => ℓ1 (Z t1 ω)) 2 P) atTop (𝓝 0) :=
    eLpNorm_two_tendsto (fun N => (hXmem N).aestronglyMeasurable.sub ha1m) hconv1
  have hL2 : Tendsto (fun N => eLpNorm (Y N - fun ω => ℓ2 (Z t2 ω)) 2 P) atTop (𝓝 0) :=
    eLpNorm_two_tendsto (fun N => (hYmem N).aestronglyMeasurable.sub hb2m) hconv2
  have ha1 : MemLp (fun ω => ℓ1 (Z t1 ω)) 2 P := memLp_two_of_tendsto ha1m hXmem hL1
  have hb2 : MemLp (fun ω => ℓ2 (Z t2 ω)) 2 P := memLp_two_of_tendsto hb2m hYmem hL2
  have hlim2 := tendsto_integral_mul_L2 ha1 hb2 hXmem hYmem hL1 hL2
  -- the covariance of the Riemann sums
  have hcov : ∀ N : ℕ, ∫ ω, X N ω * Y N ω ∂P = ∑ i ∈ Finset.range (N + 1),
      ∫ σ in Set.Icc (part t1 t2 (N + 1) i) (part t1 t2 (N + 1) (i + 1)), Dd σ (u1 N i) (u2 N i) := by
    intro N
    have e : ∀ ω, X N ω * Y N ω = (∑ i ∈ Finset.range (N + 1), incr G (part t1 t2 (N + 1)) (u1 N) i ω) *
        (∑ k ∈ Finset.range (2 * (N + 1)), incr G (part t1 t2 (N + 1)) (u2 N) k ω) := by
      intro ω; rw [hXe N ω, hYe N ω]
    simp_rw [e]
    exact cov_sum_nat hG' (hpmono N) (hp0 N) (by omega : N + 1 ≤ 2 * (N + 1)) (hpT N _ le_rfl) _ _
  -- the limit of the cell integrals
  have hlim1 : Tendsto (fun N : ℕ => ∫ ω, X N ω * Y N ω ∂P) atTop
      (𝓝 (∫ r in Set.Icc 0 t1, Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2))) := by
    rcases h1.1.eq_or_lt with h0 | hpos
    · -- `t₁ = 0`
      have ht0 : t1 = 0 := h0.symm
      have hz : ∀ N : ℕ, ∫ ω, X N ω * Y N ω ∂P = 0 := by
        intro N
        rw [hcov N]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have e1 : part t1 t2 (N + 1) i = 0 := by rw [part_of_le (by omega), ht0]; simp
        have e2 : part t1 t2 (N + 1) (i + 1) = 0 := by rw [part_of_le (by omega), ht0]; simp
        rw [e1, e2]
        simp
      have hI : ∫ r in Set.Icc 0 t1, Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2) = 0 := by
        rw [ht0]; simp
      simp_rw [hz]
      rw [hI]
      exact tendsto_const_nhds
    · -- `t₁ > 0`
      have hB10 : 0 ≤ detConst T K * ‖ℓ1‖ := mul_nonneg (detConst_pos T K).le (norm_nonneg _)
      have hB20 : 0 ≤ detConst T K * ‖ℓ2‖ := mul_nonneg (detConst_pos T K).le (norm_nonneg _)
      have hB1 : ∀ s ∈ Set.Icc 0 t1, ‖pullbackVec S t1 s ℓ1‖ ≤ detConst T K * ‖ℓ1‖ := fun s hs =>
        norm_pullback_le hT hS hs.1 hs.2 h1.2 ℓ1
      have hB2 : ∀ s ∈ Set.Icc 0 t1, ‖pullbackVec S t2 s ℓ2‖ ≤ detConst T K * ‖ℓ2‖ := fun s hs =>
        norm_pullback_le hT hS hs.1 (hs.2.trans h12) h2.2 ℓ2
      have hcells := cells_tendsto hpos
        (Φ := fun σ s => Db σ (pullbackVec S t1 s ℓ1) (pullbackVec S t2 s ℓ2))
        (β := fun σ => traceNormForm (Db σ) * ((detConst T K * ‖ℓ1‖) * (detConst T K * ‖ℓ2‖)))
        (fun s => hDb.meas _ _) ?_ ?_ ?_
      · refine hcells.1.congr fun N => ?_
        rw [hcov N]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hpi : part t1 t2 (N + 1) i = t1 * i / ((N : ℝ) + 1) := by
          rw [part_of_le (by omega)]; push_cast; rfl
        have hpi1 : part t1 t2 (N + 1) (i + 1) = t1 * ((i : ℝ) + 1) / ((N : ℝ) + 1) := by
          rw [part_of_le (by omega)]; push_cast; rfl
        have hle : part t1 t2 (N + 1) (i + 1) ≤ t1 := by
          calc part t1 t2 (N + 1) (i + 1) ≤ part t1 t2 (N + 1) (N + 1) := hpmono N (by omega)
            _ = t1 := part_M (Nat.succ_pos N)
        simp only [hu1, hu2, hpi, hpi1]
        refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
        have hσT : σ ≤ T := by
          have := hσ.2
          rw [← hpi1] at this
          exact this.trans (hle.trans h1.2)
        simp only [hDd, if_pos hσT]
      · intro σ hσ s hs
        have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1, hσ.2.trans h1.2⟩
        calc |Db σ (pullbackVec S t1 s ℓ1) (pullbackVec S t2 s ℓ2)|
            ≤ traceNormForm (Db σ) * (‖pullbackVec S t1 s ℓ1‖ * ‖pullbackVec S t2 s ℓ2‖) :=
              psd_apply_le (hDb.traceClass σ hσT) _ _
          _ ≤ traceNormForm (Db σ) * ((detConst T K * ‖ℓ1‖) * (detConst T K * ‖ℓ2‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hB1 s hs) (hB2 s hs) (norm_nonneg _) hB10)
                (traceNormForm_nonneg _)
      · exact (hDb.int.mono_set (Set.Icc_subset_Icc_right h1.2)).mul_const _
      · intro σ hσ
        have hσ1 : σ ∈ Set.Icc 0 t1 := Set.Ioc_subset_Icc_self hσ
        have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1.le, hσ.2.trans h1.2⟩
        have hid : Tendsto (id : ℝ → ℝ) (𝓝[Set.Icc 0 t1] σ) (𝓝 σ) :=
          (tendsto_id (x := 𝓝[Set.Icc 0 t1] σ)).mono_right nhdsWithin_le_nhds
        have hm1 : ∀ᶠ s in 𝓝[Set.Icc 0 t1] σ, s ∈ Set.Icc 0 t1 := self_mem_nhdsWithin
        have hm2 : ∀ᶠ s in 𝓝[Set.Icc 0 t1] σ, s ∈ Set.Icc 0 t2 := by
          filter_upwards [hm1] with s hs
          exact ⟨hs.1, hs.2.trans h12⟩
        refine psd_tendsto_weak (hDb.traceClass σ hσT) (fun s => pullbackVec S t1 s ℓ1)
          (fun s => pullbackVec S t2 s ℓ2) _ _ (B := max (detConst T K * ‖ℓ1‖) (detConst T K * ‖ℓ2‖))
          (le_max_of_le_left hB10) ?_ ?_ ?_ ?_
        · filter_upwards [hm1] with s hs using (hB1 s hs).trans (le_max_left _ _)
        · filter_upwards [hm1] with s hs using (hB2 s hs).trans (le_max_right _ _)
        · intro x
          exact pullback_weak_tendsto hev h1 ℓ1 id hσ1 hm1 hid x
        · intro x
          exact pullback_weak_tendsto hev h2 ℓ2 id ⟨hσ.1.le, hσ.2.trans h12⟩ hm2 hid x
  exact tendsto_nhds_unique hlim2 hlim1

theorem cov_formula {S : EvolData H E} {T K : ℝ} (hT : 0 ≤ T) (hS : S.MaxHyp T K)
    {G : ℝ → Ω → H} {Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hDb : IsDetCovDensity T Db)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => if r ≤ T then Db r else 0))
    {Z : ℝ → Ω → E} (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    {t1 t2 : ℝ} (h1 : t1 ∈ Set.Icc (0 : ℝ) T) (h2 : t2 ∈ Set.Icc (0 : ℝ) T)
    (ℓ1 ℓ2 : E →L[ℝ] ℝ) :
    ∫ ω, ℓ1 (Z t1 ω) * ℓ2 (Z t2 ω) ∂P =
      ∫ r in Set.Icc 0 (min t1 t2), Db r (pullbackVec S t1 r ℓ1) (pullbackVec S t2 r ℓ2) := by
  rcases le_total t1 t2 with h12 | h21
  · rw [min_eq_left h12]
    exact cov_formula_le hT hS hDb hG hZ hZm h1 h2 h12 ℓ1 ℓ2
  · rw [min_eq_right h21]
    have := cov_formula_le hT hS hDb hG hZ hZm h2 h1 h21 ℓ2 ℓ1
    simp_rw [mul_comm (ℓ1 _)]
    rw [this]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc 0 T := ⟨hr.1, hr.2.trans h2.2⟩
    exact (hDb.traceClass r hrT).symm _ _

end Formula

end HRS.Uniform.Q45
