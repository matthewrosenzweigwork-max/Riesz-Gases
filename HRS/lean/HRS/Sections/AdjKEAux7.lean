import HRS.Sections.AdjKEAux6

/-!
# ADJKE part 7: `adjke_pair_identification`

A.s. `⟨Z_t, e_k⟩ = √N ∫_0^t ∂_jU^{r,t}e_k(x_i(r)) dW'` for the stochastic convolution `Z_t` of the particle martingale,
assuming only measurability of `⟨Z_t, e_k⟩` (without it the statement is false, `IsStochConv` involves a lower integral).
Port of `GF.gfb3_pair_identification_aem`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjke_pair_identification (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hn : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → NegSobolev d m)
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (M t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hV : IsDualEvolution htr.dyn ρ m Vev)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (Zt : Ω → NegSobolev d m)
    (hZ : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t Zt)
    (k : NonzeroLattice d)
    (hZm : AEMeasurable (fun ω => NegSobolev.eval (Zt ω) (Torus.realMode k)) P) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zt ω) (Torus.realMode k) = Real.sqrt N *
      itoIntegral P ℱ W' (empiricalNoiseIntegrand htr.dyn t
        (fun r => propagator htr.dyn ρ r t (Torus.realMode k)) X) t ω := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  set φ : Torus d → ℝ := Torus.realMode k with hφdef
  have hφ : Torus.IsSmooth φ := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
  obtain ⟨Λ₂, -, -, hpack⟩ := dyncmp_adjoint_package hd htr T
  obtain ⟨Cφ, hCφ⟩ := hpack φ hφ
  have hfC : IsClassicalAdjointSolution htr.dyn ρ t φ (fun r => propagator htr.dyn ρ r t φ) :=
    (hCφ t ht).1
  set f : ℝ → Torus d → ℝ := fun r => propagator htr.dyn ρ r t φ with hfdef
  have hC := hfC.isC12Test
  have hW := hF.brownian
  -- regularity of `f r`
  set j : ℕ := ⌈m⌉₊ + d + 2 with hjdef
  have hj : (d : ℝ) + 2 ≤ j := by
    rw [hjdef]; push_cast
    have : (0 : ℝ) ≤ ⌈m⌉₊ := Nat.cast_nonneg _
    linarith
  have hmj : m ≤ (j : ℝ) + 5 := by
    rw [hjdef]; push_cast
    have := Nat.le_ceil m
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hψm : ∀ r ∈ Set.Icc (0 : ℝ) t, MemSobolev m (f r) := fun r hr =>
    HRS.PDE.MFAdjoint.memSobolev_mono_idx (adjke_prop_dom hd htr j hj hφ hr.1 hr.2).2 hmj
  have hf2 : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (f r) := fun r hr => hC.c2 r hr
  have htT : t ≤ T := ht.2
  have hmemT : ∀ τ ∈ Set.Icc (0 : ℝ) t, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans htT⟩
  -- the pairing of the particle martingale with `f r` is an Itô integral
  have hpair : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ᵐ ω ∂P,
      NegSobolev.eval (M τ ω) (f r) = itoIntegral P ℱ W' (adjkeEta
        ((Real.sqrt N * Real.sqrt (2 * β⁻¹)) / N) X (f r)) τ ω :=
    fun r hr τ hτ => adjke_pairing hd htr hn T hN P hF hT.le M hMid (hf2 r hr) (hψm r hr) (hmemT τ hτ)
  set c0 : ℝ := Real.sqrt N * Real.sqrt (2 * β⁻¹) with hc0def
  have hc0 : c0 = Real.sqrt N * Real.sqrt (2 * htr.dyn.invβ) := rfl
  set c : ℝ := c0 / N with hcdef
  set σ : ℝ := Real.sqrt N with hσ
  set E := empiricalNoiseIntegrand htr.dyn t f X with hEdef
  have hE : IsProgressiveL2 P ℱ E := isProgressiveL2_empiricalNoiseIntegrand hF.progressive ht.1 hC
  show ∀ᵐ ω ∂P, NegSobolev.eval (Zt ω) φ = σ * itoIntegral P ℱ W' E t ω
  set a : Ω → ℝ := fun ω => NegSobolev.eval (Zt ω) φ with ha
  set e : Ω → ℝ := fun ω => σ * itoIntegral P ℱ W' E t ω with he
  have he_meas : AEMeasurable e P :=
    (((adapted_itoIntegral P ℱ W' E t).mono (ℱ.le t) le_rfl).const_mul σ).aemeasurable
  set Cφ' : ℝ := sobolevNorm m φ with hCφ'
  have hCφ0 : 0 ≤ Cφ' := Real.sqrt_nonneg _
  -- main estimate
  have hmain : ∀ u : ℝ, 0 < u → ∫⁻ ω, ‖a ω - e ω‖ₑ ^ 2 ∂P ≤
      2 * (ENNReal.ofReal u * ENNReal.ofReal Cφ' ^ 2) +
        2 * (ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2))) := by
    intro u hu
    obtain ⟨δ, hδ, hδZ⟩ := hZ u hu
    obtain ⟨δ', hδ', huc⟩ := gfb3_uc hC u hu
    set μ : ℝ := min δ δ' with hμ
    have hμpos : 0 < μ := lt_min hδ hδ'
    set n : ℕ := ⌈t / μ⌉₊ + 1 with hn'
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hstep : t / n < μ := by
      rw [div_lt_iff₀ hnpos]
      have h1 : t / μ ≤ ⌈t / μ⌉₊ := Nat.le_ceil _
      have h2 : (⌈t / μ⌉₊ : ℝ) < n := by rw [hn']; push_cast; linarith
      have h3 : t / μ < n := lt_of_le_of_lt h1 h2
      rw [div_lt_iff₀ hμpos] at h3
      linarith
    have hstepδ : t / n < δ := hstep.trans_le (min_le_left _ _)
    have hstepδ' : t / n < δ' := hstep.trans_le (min_le_right _ _)
    set r := gfb3_part t n with hr
    set b : Ω → ℝ := fun ω => NegSobolev.eval (riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
      M t r ω) φ with hb
    have hnn : ∀ i : Fin (n + 1), 0 ≤ r i := gfb3_part_nonneg ht.1
    have hle : ∀ i : Fin (n + 1), r i ≤ t := gfb3_part_le ht.1 hn1
    have hmem : ∀ i : Fin (n + 1), r i ∈ Set.Icc (0 : ℝ) t := fun i => ⟨hnn i, hle i⟩
    have hΨ : ∀ i : Fin n, IsProgressiveL2 P ℱ (adjkeEta c X (f (r i.castSucc))) := fun i =>
      adjke_eta_L2 _ hF.progressive (hf2 _ (hmem _))
    have hrs := gfb3_ito_rsum hW (fun i : Fin n => r i.castSucc) (fun i : Fin n => r i.succ)
      (fun i => hnn _) (fun i => gfb3_part_mono ht.1 (Fin.castSucc_le_succ i))
      (fun i => adjkeEta c X (f (r i.castSucc))) hΨ Finset.univ
    -- the Riemann sum pairing (deterministic)
    have hRS : ∀ ω, b ω = ∑ i : Fin n, (NegSobolev.eval (M (r i.succ) ω) (f (r i.castSucc)) -
        NegSobolev.eval (M (r i.castSucc) ω) (f (r i.castSucc))) := by
      intro ω
      show NegSobolev.eval (riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) φ = _
      unfold riemannSum
      rw [eval_lpFun _ hφm, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← eval_lpFun _ hφm]
      have h0 : 0 ≤ r i.castSucc := hnn _
      have h1 : r i.castSucc ≤ t := hle _
      rw [hV (r i.castSucc) t h0 h1 _ φ hφ]
      show NegSobolev.eval _ (f (r i.castSucc)) = _
      rw [eval_lpFun _ (hψm _ (hmem i.castSucc)), eval_lpFun _ (hψm _ (hmem i.castSucc)),
        eval_lpFun _ (hψm _ (hmem i.castSucc)), ← inner_sub_left]
      rfl
    -- Riemann sums are Itô integrals of the piecewise integrand
    have hbn : ∀ᵐ ω ∂P, b ω = itoIntegral P ℱ W' (fun s ω k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) t ω := by
      have hall : ∀ᵐ ω ∂P, ∀ i : Fin n,
          NegSobolev.eval (M (r i.succ) ω) (f (r i.castSucc)) =
            itoIntegral P ℱ W' (adjkeEta c X (f (r i.castSucc))) (r i.succ) ω ∧
          NegSobolev.eval (M (r i.castSucc) ω) (f (r i.castSucc)) =
            itoIntegral P ℱ W' (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) ω := by
        rw [ae_all_iff]
        intro i
        filter_upwards [hpair _ (hmem i.castSucc) _ (hmem i.succ),
          hpair _ (hmem i.castSucc) _ (hmem i.castSucc)] with ω h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hall, hrs.2] with ω hω h2
      rw [hRS ω, h2 t]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [min_eq_right (hle i.succ), min_eq_right (hle i.castSucc), (hω i).1, (hω i).2]
    have hΞ1 : IsProgressiveL2 P ℱ (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
        ((-σ) • E s ω)) := hrs.1.add (hE.smul (-σ))
    have hdiff : ∀ᵐ ω ∂P, b ω - e ω = itoIntegral P ℱ W' (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
        ((-σ) • E s ω)) t ω := by
      filter_upwards [hbn, itoIntegral_add hW hrs.1 (hE.smul (-σ)), itoIntegral_smul hW hE (-σ)]
        with ω h1 h2 h3
      rw [h2 t, h3 t, ← h1]
      simp only [he]
      ring
    have hb_meas : AEMeasurable b P := by
      have : AEMeasurable (fun ω => itoIntegral P ℱ W' (fun s ω k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
          restrictFun (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) t ω) P :=
        ((adapted_itoIntegral P ℱ W' _ t).mono (ℱ.le t) le_rfl).aemeasurable
      exact this.congr (hbn.mono fun ω h => h.symm)
    have hb1 : ∫⁻ ω, ‖a ω - b ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal u * ENNReal.ofReal Cφ' ^ 2 := by
      have hpt : ∀ ω, ‖a ω - b ω‖ₑ ^ 2 ≤
          ‖Zt ω - riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω‖ₑ ^ 2 *
            ENNReal.ofReal Cφ' ^ 2 := by
        intro ω
        have h1 : a ω - b ω = NegSobolev.eval (Zt ω - riemannSum Vev
            (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) φ := by
          show NegSobolev.eval (Zt ω) φ - NegSobolev.eval (riemannSum Vev
            (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) φ = _
          rw [eval_lpFun (Zt ω) hφm, eval_lpFun (riemannSum Vev
            (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) hφm, eval_lpFun (Zt ω - riemannSum Vev
            (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) hφm, inner_sub_left]
        have h2 := adjke_abs_eval_le (Zt ω - riemannSum Vev
          (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) hφm
        rw [h1]
        calc ‖NegSobolev.eval (Zt ω - riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) φ‖ₑ ^ 2
            = (ENNReal.ofReal |NegSobolev.eval (Zt ω - riemannSum Vev
                (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω) φ|) ^ 2 := by
              rw [Real.enorm_eq_ofReal_abs]
          _ ≤ (ENNReal.ofReal (‖Zt ω - riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω‖ *
                Cφ')) ^ 2 :=
              pow_le_pow_left' (ENNReal.ofReal_le_ofReal h2) 2
          _ = _ := by
              rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_pow]
      calc ∫⁻ ω, ‖a ω - b ω‖ₑ ^ 2 ∂P
          ≤ ∫⁻ ω, ‖Zt ω - riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω‖ₑ ^ 2 *
              ENNReal.ofReal Cφ' ^ 2 ∂P :=
            lintegral_mono hpt
        _ = (∫⁻ ω, ‖Zt ω - riemannSum Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M t r ω‖ₑ ^ 2 ∂P) *
              ENNReal.ofReal Cφ' ^ 2 :=
            lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        _ ≤ ENNReal.ofReal u * ENNReal.ofReal Cφ' ^ 2 :=
            mul_le_mul' (hδZ n r gfb3_part_zero (gfb3_part_last hn1) (gfb3_part_mono ht.1)
              (fun i => by rw [gfb3_part_step hn1 i]; exact hstepδ)).le le_rfl
    have hb2 : ∫⁻ ω, ‖b ω - e ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2)) := by
      calc ∫⁻ ω, ‖b ω - e ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, ‖itoIntegral P ℱ W' (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
              restrictFun (adjkeEta c X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
              ((-σ) • E s ω)) t ω‖ₑ ^ 2 ∂P :=
            lintegral_congr_ae (by filter_upwards [hdiff] with ω h; rw [h])
        _ = sqIntegralOn P _ t := lintegral_itoIntegral_sq hW hΞ1 t
        _ ≤ _ := adjke_Xi_bound htr.dyn N c0 hc0 P X ht.1 hn1 (f := f) (ft := fun _ _ => 0) huc hstepδ'
    have hsplit : ∫⁻ ω, ‖a ω - e ω‖ₑ ^ 2 ∂P ≤
        2 * ∫⁻ ω, ‖a ω - b ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖b ω - e ω‖ₑ ^ 2 ∂P := by
      have := lintegral_enorm_sq_add_le' (P := P) (hZm.sub hb_meas) (hb_meas.sub he_meas)
      simpa [sub_add_sub_cancel] using this
    calc ∫⁻ ω, ‖a ω - e ω‖ₑ ^ 2 ∂P ≤ _ := hsplit
      _ ≤ _ := by gcongr
  -- conclusion
  have hzero : ∫⁻ ω, ‖a ω - e ω‖ₑ ^ 2 ∂P = 0 := by
    refine le_antisymm ?_ zero_le
    have h1 : Tendsto (fun u : ℝ => ENNReal.ofReal u) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun u : ℝ => ENNReal.ofReal (c ^ 2 * u ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous fun u : ℝ => ENNReal.ofReal (c ^ 2 * u ^ 2) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hK : ENNReal.ofReal Cφ' ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hK)
    have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr (ENNReal.natCast_ne_top (N * d)))
    have h6 := ENNReal.Tendsto.const_mul h5 (Or.inr (ENNReal.ofReal_ne_top (r := t)))
    have h2' := ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have h6' := ENNReal.Tendsto.const_mul h6 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have hg := h2'.add h6'
    have hg' : Tendsto (fun u : ℝ => 2 * (ENNReal.ofReal u * ENNReal.ofReal Cφ' ^ 2) +
        2 * (ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2))))
        (𝓝[>] 0) (𝓝 0) := by simpa using hg
    exact ge_of_tendsto hg' (eventually_nhdsWithin_of_forall fun u hu => hmain u hu)
  have h0 := ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hZm.sub he_meas) hzero
  filter_upwards [h0] with ω hω
  exact sub_eq_zero.1 hω

end HRS.AdjK
