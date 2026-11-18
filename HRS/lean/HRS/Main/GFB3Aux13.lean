import HRS.Main.GFB3Aux12

/-!
# Packet GFB3, part 13: `gf_pair_identification` assembled (with `hZm`; see `GFB3Aux12` for why it is needed)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q54c

variable {d : ℕ}

lemma gfb3_abs_eval_le {m : ℝ} (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : MemSobolev m φ) :
    |NegSobolev.eval F φ| ≤ ‖F‖ * sobolevNorm m φ := by
  rw [eval_lpFun F hφ]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_lpFun_le m φ) (norm_nonneg _))

theorem gfb3_pair_identification_aem (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ)
    (m K : ℝ) (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hF : IsFilteredSolution P ℱ W' W X)
    (Mart : ℝ → Ω → NegSobolev d (S.γ : ℝ))
    (hMart : IsHilbertItoIntegral P ℱ W'
      (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r))) Mart)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) S.T) (Zt : Ω → NegSobolev d m)
    (hZ : IsStochConv P EV.VE EV.j Mart 0 t Zt) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (hZm : AEMeasurable (fun ω => NegSobolev.eval (Zt ω) φ) P) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zt ω) φ = sigN S N *
      empiricalMartingale P ℱ W' (S.dynM M N) t
        (fun r => propagator (S.dynM M N) (S.ρ N) r t φ) X ((Real.toNNReal t : ℝ≥0) : ℝ) ω := by
  classical
  have hγm := gfb3_m_ge_gamma S M N m K EV hEV
  obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
  have hex : ∃ f, IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f :=
    (hEV.adjoint 0 t le_rfl ht.1 ht.2 φ hφ2 hφm).1
  set f : ℝ → Torus d → ℝ := fun r => propagator (S.dynM M N) (S.ρ N) r t φ with hfdef
  have hfC : IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f := by
    have e : f = hex.choose := by
      funext r
      simp only [hfdef, propagator]
      rw [dif_pos hex]
    rw [e]; exact hex.choose_spec
  have hC := hfC.isC12Test
  have hW := hF.brownian
  have hψm : ∀ r ∈ Set.Icc (0 : ℝ) t, MemSobolev (S.γ : ℝ) (f r) := fun r hr =>
    HRS.PDE.MFAdjoint.memSobolev_mono_idx (hEV.adjoint r t hr.1 hr.2 ht.2 φ hφ2 hφm).2.1 hγm
  -- the pairing of the particle martingale with `lpFun γ (f r)` is an Itô integral
  have hpair : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ τ : ℝ, 0 ≤ τ →
      (fun ω => inner ℝ (Mart τ ω) (lpFun (S.γ : ℝ) (f r))) =ᵐ[P]
        itoIntegral P ℱ W' (gfb3_eta S N X (f r)) τ := by
    intro r hr τ hτ
    have hr2 : Torus.IsCk 2 (f r) := hC.c2 r hr
    have hc : Continuous (f r) :=
      Torus.continuous_of_continuous_lift (show ContDiff ℝ 2 (Torus.lift (f r)) from hr2).continuous
    have h1 : Torus.IsCk 1 (f r) := hr2.of_le (by norm_num)
    have hfun : (fun r' ω (k : Fin N × Fin d) => inner ℝ (noiseIntegrand (S.γ : ℝ) (noiseScale S N)
        (fun r => X (Real.toNNReal r)) r' ω k) (lpFun (S.γ : ℝ) (f r))) = gfb3_eta S N X (f r) := by
      funext r' ω k
      exact gfb3_eta_pair S N X (hψm r hr) hc h1 r' ω k
    have hξ' : IsProgressiveL2 P ℱ (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
        inner ℝ (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r)) r' ω k)
          (lpFun (S.γ : ℝ) (f r))) := by
      have := gfb3_isProgressiveL2_restrict_univ
        (gfb3_eta_L2 S N X hF.progressive hr2 (P := P) (ℱ := ℱ))
      have heq : (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
          inner ℝ (noiseIntegrand (S.γ : ℝ) (noiseScale S N) (fun r => X (Real.toNNReal r)) r' ω k)
            (lpFun (S.γ : ℝ) (f r))) =
          fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) => gfb3_eta S N X (f r) r' ω k := by
        funext r' ω k
        exact gfb3_eta_pair S N X (hψm r hr) hc h1 r' ω k
      rw [heq]
      exact this
    have := gfb3_pair_ito hW hMart (lpFun (S.γ : ℝ) (f r)) hξ' hτ
    rwa [hfun] at this
  set c : ℝ := noiseScale S N / N with hc
  set σ : ℝ := sigN S N with hσ
  set E := empiricalNoiseIntegrand (S.dynM M N) t f X with hEdef
  have hE : IsProgressiveL2 P ℱ E := isProgressiveL2_empiricalNoiseIntegrand hF.progressive ht.1 hC
  have hT : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1
  rw [hT]
  show ∀ᵐ ω ∂P, NegSobolev.eval (Zt ω) φ = sigN S N * itoIntegral P ℱ W' E t ω
  set a : Ω → ℝ := fun ω => NegSobolev.eval (Zt ω) φ with ha
  set e : Ω → ℝ := fun ω => σ * itoIntegral P ℱ W' E t ω with he
  have he_meas : AEMeasurable e P :=
    (((adapted_itoIntegral P ℱ W' E t).mono (ℱ.le t) le_rfl).const_mul σ).aemeasurable
  set Cφ : ℝ := sobolevNorm m φ with hCφ
  have hCφ0 : 0 ≤ Cφ := Real.sqrt_nonneg _
  -- main estimate
  have hmain : ∀ u : ℝ, 0 < u → ∫⁻ ω, ‖a ω - e ω‖ₑ ^ 2 ∂P ≤
      2 * (ENNReal.ofReal u * ENNReal.ofReal Cφ ^ 2) +
        2 * (ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2))) := by
    intro u hu
    obtain ⟨δ, hδ, hδZ⟩ := hZ u hu
    obtain ⟨δ', hδ', huc⟩ := gfb3_uc hC u hu
    set μ : ℝ := min δ δ' with hμ
    have hμpos : 0 < μ := lt_min hδ hδ'
    set n : ℕ := ⌈t / μ⌉₊ + 1 with hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hstep : t / n < μ := by
      rw [div_lt_iff₀ hnpos]
      have h1 : t / μ ≤ ⌈t / μ⌉₊ := Nat.le_ceil _
      have h2 : (⌈t / μ⌉₊ : ℝ) < n := by rw [hn]; push_cast; linarith
      have h3 : t / μ < n := lt_of_le_of_lt h1 h2
      rw [div_lt_iff₀ hμpos] at h3
      linarith
    have hstepδ : t / n < δ := hstep.trans_le (min_le_left _ _)
    have hstepδ' : t / n < δ' := hstep.trans_le (min_le_right _ _)
    set r := gfb3_part t n with hr
    set b : Ω → ℝ := fun ω => NegSobolev.eval (riemannSum EV.VE EV.j Mart t r ω) φ with hb
    have hnn : ∀ i : Fin (n + 1), 0 ≤ r i := gfb3_part_nonneg ht.1
    have hle : ∀ i : Fin (n + 1), r i ≤ t := gfb3_part_le ht.1 hn1
    have hmem : ∀ i : Fin (n + 1), r i ∈ Set.Icc (0 : ℝ) t := fun i => ⟨hnn i, hle i⟩
    have hΨ : ∀ i : Fin n, IsProgressiveL2 P ℱ (gfb3_eta S N X (f (r i.castSucc))) := fun i =>
      gfb3_eta_L2 S N X hF.progressive (hC.c2 _ (hmem _))
    have hrs := gfb3_ito_rsum hW (fun i : Fin n => r i.castSucc) (fun i : Fin n => r i.succ)
      (fun i => hnn _) (fun i => gfb3_part_mono ht.1 (Fin.castSucc_le_succ i))
      (fun i => gfb3_eta S N X (f (r i.castSucc))) hΨ Finset.univ
    -- Riemann sums are Itô integrals of the piecewise integrand
    have hbn : ∀ᵐ ω ∂P, b ω = itoIntegral P ℱ W' (fun s ω k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) t ω := by
      have hall : ∀ᵐ ω ∂P, ∀ i : Fin n,
          inner ℝ (Mart (r i.succ) ω) (lpFun (S.γ : ℝ) (f (r i.castSucc))) =
            itoIntegral P ℱ W' (gfb3_eta S N X (f (r i.castSucc))) (r i.succ) ω ∧
          inner ℝ (Mart (r i.castSucc) ω) (lpFun (S.γ : ℝ) (f (r i.castSucc))) =
            itoIntegral P ℱ W' (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) ω := by
        rw [ae_all_iff]
        intro i
        filter_upwards [hpair _ (hmem i.castSucc) _ (hnn i.succ),
          hpair _ (hmem i.castSucc) _ (hnn i.castSucc)] with ω h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hall, hrs.2] with ω hω h2
      show NegSobolev.eval (riemannSum EV.VE EV.j Mart t r ω) φ = _
      rw [gfb3_riemann_eval S M N m K EV hEV Mart t ht φ hφ r gfb3_part_zero
        (gfb3_part_last hn1) (gfb3_part_mono ht.1) ω, h2 t]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [min_eq_right (hle i.succ), min_eq_right (hle i.castSucc)]
      show NegSobolev.eval _ (f (r i.castSucc)) = _
      rw [eval_lpFun _ (hψm _ (hmem i.castSucc)), ← (hω i).1, ← (hω i).2, inner_sub_left]
    have hΞ1 : IsProgressiveL2 P ℱ (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
        ((-σ) • E s ω)) := hrs.1.add (hE.smul (-σ))
    have hdiff : ∀ᵐ ω ∂P, b ω - e ω = itoIntegral P ℱ W' (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
        restrictFun (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
        ((-σ) • E s ω)) t ω := by
      filter_upwards [hbn, itoIntegral_add hW hrs.1 (hE.smul (-σ)), itoIntegral_smul hW hE (-σ)]
        with ω h1 h2 h3
      rw [h2 t, h3 t, ← h1]
      simp only [he]
      ring
    have hb_meas : AEMeasurable b P := by
      have : AEMeasurable (fun ω => itoIntegral P ℱ W' (fun s ω k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
          restrictFun (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) t ω) P :=
        ((adapted_itoIntegral P ℱ W' _ t).mono (ℱ.le t) le_rfl).aemeasurable
      exact this.congr (hbn.mono fun ω h => h.symm)
    have hb1 : ∫⁻ ω, ‖a ω - b ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal u * ENNReal.ofReal Cφ ^ 2 := by
      have hpt : ∀ ω, ‖a ω - b ω‖ₑ ^ 2 ≤
          ‖Zt ω - riemannSum EV.VE EV.j Mart t r ω‖ₑ ^ 2 * ENNReal.ofReal Cφ ^ 2 := by
        intro ω
        have h1 : a ω - b ω = NegSobolev.eval (Zt ω - riemannSum EV.VE EV.j Mart t r ω) φ :=
          (gf_eval_sub_proof _ _ hφ).symm
        have h2 := gfb3_abs_eval_le (Zt ω - riemannSum EV.VE EV.j Mart t r ω) hφm
        rw [h1]
        calc ‖NegSobolev.eval (Zt ω - riemannSum EV.VE EV.j Mart t r ω) φ‖ₑ ^ 2
            = (ENNReal.ofReal |NegSobolev.eval (Zt ω - riemannSum EV.VE EV.j Mart t r ω) φ|) ^ 2 := by
              rw [Real.enorm_eq_ofReal_abs]
          _ ≤ (ENNReal.ofReal (‖Zt ω - riemannSum EV.VE EV.j Mart t r ω‖ * Cφ)) ^ 2 :=
              pow_le_pow_left' (ENNReal.ofReal_le_ofReal h2) 2
          _ = _ := by
              rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, mul_pow]
      calc ∫⁻ ω, ‖a ω - b ω‖ₑ ^ 2 ∂P
          ≤ ∫⁻ ω, ‖Zt ω - riemannSum EV.VE EV.j Mart t r ω‖ₑ ^ 2 * ENNReal.ofReal Cφ ^ 2 ∂P :=
            lintegral_mono hpt
        _ = (∫⁻ ω, ‖Zt ω - riemannSum EV.VE EV.j Mart t r ω‖ₑ ^ 2 ∂P) * ENNReal.ofReal Cφ ^ 2 :=
            lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        _ ≤ ENNReal.ofReal u * ENNReal.ofReal Cφ ^ 2 :=
            mul_le_mul' (hδZ n r gfb3_part_zero (gfb3_part_last hn1) (gfb3_part_mono ht.1)
              (fun i => by rw [gfb3_part_step hn1 i]; exact hstepδ)).le le_rfl
    have hb2 : ∫⁻ ω, ‖b ω - e ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2)) := by
      calc ∫⁻ ω, ‖b ω - e ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, ‖itoIntegral P ℱ W' (fun s ω => (fun k => ∑ i ∈ (Finset.univ : Finset (Fin n)),
              restrictFun (gfb3_eta S N X (f (r i.castSucc))) (r i.castSucc) (r i.succ) Set.univ s ω k) +
              ((-σ) • E s ω)) t ω‖ₑ ^ 2 ∂P :=
            lintegral_congr_ae (by filter_upwards [hdiff] with ω h; rw [h])
        _ = sqIntegralOn P _ t := lintegral_itoIntegral_sq hW hΞ1 t
        _ ≤ _ := gfb3_Xi_bound S M N P X ht.1 hn1 (f := f) (ft := fun _ _ => 0) huc hstepδ'
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
    have hK : ENNReal.ofReal Cφ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hK)
    have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr (ENNReal.natCast_ne_top (N * d)))
    have h6 := ENNReal.Tendsto.const_mul h5 (Or.inr (ENNReal.ofReal_ne_top (r := t)))
    have h2' := ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have h6' := ENNReal.Tendsto.const_mul h6 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    have hg := h2'.add h6'
    have hg' : Tendsto (fun u : ℝ => 2 * (ENNReal.ofReal u * ENNReal.ofReal Cφ ^ 2) +
        2 * (ENNReal.ofReal t * (((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c ^ 2 * u ^ 2))))
        (𝓝[>] 0) (𝓝 0) := by simpa using hg
    exact ge_of_tendsto hg' (eventually_nhdsWithin_of_forall fun u hu => hmain u hu)
  have h0 := ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hZm.sub he_meas) hzero
  filter_upwards [h0] with ω hω
  exact sub_eq_zero.1 hω

end HRS.GF
