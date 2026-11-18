import HRS.MH.WpSpec2
import HRS.MH.WpP2
import HRS.Main.GFFinal1

/-!
# P4: `HRS.MH.Wp.gff_stage2_p` (order-`p` stage 2, Wasserstein part only)

Copy-edit of `HRS.GF.gff_stage2` (GFFinal1.lean:164-407) at order `p ≥ 2`, with the smooth half deleted.
The second enlargement, `hGb`, `Zb`, `hXform`, `hlaw1`, `hL`/`hL'` and `hD`/`hSd` are as in the original.
The single Wasserstein estimate is `gfwp_wasserstein_comparison_proof` (P2, WpP2.lean), with constant `Cw`.
The cost term `(∫⁻ (∫⁻ cost)^{p/2})^{1/p}` is moved from `P₂` to `P₁` by `lintegral_comp_mp`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c

set_option maxHeartbeats 1600000 in
theorem gff_stage2_p_proof :
    type_of% @HRS.MH.Wp.gff_stage2_p := by
  intro d T K p hT hp
  have hp0 : 0 < p := by linarith
  obtain ⟨Cw, hCw0, hwp⟩ := gfwp_wasserstein_comparison_proof T K p hT hp
  refine ⟨Cw, hCw0, ?_⟩
  intro S hST M hMF N hN m hm EV hEV Ω Ω₁ mΩ mΩ₁ P _ P₁ _ ℱ₁ X₁ η' Mart Z Bm Y₀ Y h cost hcpl hcostm
  subst hST
  obtain ⟨Cm, hCm0, hmax⟩ := Q45.maximal_estimate_meas S.T K hT
  obtain ⟨hXad, hη', hMartM, hMart, hDet, hZ, hZc, hZm, hΞc, hΞm, hBm, hRb, hY₀m, hY, hlaw⟩ := h
  set σ := sigN S N with hσ
  set q := qN S N with hq
  set Cb := covDensT (S.γ : ℝ) q S.T (S.ρ N) with hCb
  have hγm : (d : ℝ) / 2 < (S.γ : ℝ) := by
    have h1 : 2 * d + 10 < S.γ := S.hγ
    have h2 : ((2 * d + 10 : ℕ) : ℝ) < (S.γ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmm : (d : ℝ) / 2 < m := lt_of_lt_of_le hγm hm
  -- the Gaussian coupling on a second enlargement
  obtain ⟨Ω₂, mΩ₂, P₂, π, ℱ₂, Gb, Sd, hc⟩ := hcpl
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π (P₂ : Measure Ω₂) P₁ := hc.preserving
  -- the Gaussian martingale, with the untruncated deterministic covariation
  have hGb : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ S.T Gb (fun r _ => Cb r) := by
    have h1 := hc.gaussian S.T hT le_rfl
    have e : (fun (r : ℝ) (_ : Ω₂) => if ENNReal.ofReal r ≤ ENNReal.ofReal S.T then Cb r else 0) =
        fun r _ => Cb r := by
      funext r _
      exact covDensT_truncated hT _ r
    rw [e] at h1
    exact h1
  -- its stochastic convolution
  obtain ⟨Zb₀, hZb₀, hZbc₀, hZbm₀, -⟩ := hmax Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ))
    (NegSobolev d m) EV hEV.maxHyp Gb (fun r _ => Cb r) hGb
  obtain ⟨Zb, hZbm, hZbc, hZbeq⟩ := gf_measurable_modification_proof (P₂ : Measure Ω₂) S.T Zb₀ hZbc₀ hZbm₀
  have hZb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv (P₂ : Measure Ω₂) EV.VE EV.j Gb 0 t (Zb t) :=
    fun t ht => isStochConv_congr_ae (hZb₀ t ht) (hZbeq t ht).symm
  -- measurability of the fluctuation process
  have hX₁m : ∀ t : ℝ≥0, Measurable (X₁ t) := fun t => (hXad t).mono (ℱ₁.le t) le_rfl
  have hflucm : ∀ (m' : ℝ), (d : ℝ) / 2 < m' → ∀ t : ℝ,
      Measurable (fun ω => flucProc m' σ X₁ (S.ρ N) t ω) := fun m' hm' t =>
    (gf_measurable_ofMeasureDiff_proof m' hm' (withDensityReal (S.ρ N t))).const_smul σ |>.comp
      (hX₁m (Real.toNNReal t))
  -- the data on the second enlargement
  set X₀ : Ω₂ → NegSobolev d (S.γ : ℝ) := fun ω => flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 (π ω) with hX₀
  set X₀' : Ω₂ → NegSobolev d (S.γ : ℝ) := fun ω => AN S N • η' (π ω) with hX₀'
  set Xp : ℝ → Ω₂ → NegSobolev d m := fun t ω => flucProc m σ X₁ (S.ρ N) t (π ω) with hXp
  set Zp : ℝ → Ω₂ → NegSobolev d m := fun t ω => Z t (π ω) with hZp
  set Rp : ℝ → Ω₂ → NegSobolev d m :=
    fun t ω => Xp t ω - EV.VE t 0 (EV.j (X₀ ω)) - Zp t ω with hRp
  set Xb : ℝ → Ω₂ → NegSobolev d m := fun t ω => EV.VE t 0 (EV.j (X₀' ω)) + Zb t ω with hXb
  have hπ0 : Measurable[ℱ₂ 0, ℱ₁ 0] π := Measurable.of_comap_le (hc.filtration 0)
  have hX0 : Measurable[ℱ₁ 0] (X₁ (Real.toNNReal 0)) :=
    (hXad (Real.toNNReal 0)).mono (ℱ₁.mono (by simp)) le_rfl
  have hX₀m : Measurable[ℱ₂ 0] X₀ := by
    have h1 : Measurable[ℱ₁ 0] (fun ω => flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω) :=
      ((gf_measurable_ofMeasureDiff_proof (S.γ : ℝ) hγm (withDensityReal (S.ρ N 0))).const_smul σ).comp hX0
    exact h1.comp hπ0
  have hX₀'m : Measurable[ℱ₂ 0] X₀' := (hη'.const_smul (AN S N)).comp hπ0
  have hMπm : ∀ τ, Measurable (fun ω => Mart τ (π ω)) := fun τ => (hMartM τ).comp hπ.measurable
  have hGbm : ∀ τ, Measurable (Gb τ) := fun τ =>
    gfb4_measurable_of_weak fun x => (((hGb.martingale x).stronglyAdapted τ).mono (ℱ₂.le τ)).measurable
  have hMm : ∀ τ, AEMeasurable (fun ω => EV.j (Mart τ ω)) P₁ := fun τ =>
    (EV.j.continuous.measurable.comp (hMartM τ)).aemeasurable
  have hZpS : ∀ t ∈ Set.Icc (0 : ℝ) S.T, IsStochConv (P₂ : Measure Ω₂) EV.VE EV.j
      (fun τ ω => Mart τ (π ω)) 0 t (Zp t) :=
    fun t ht => isStochConv_comp hπ (hMm) (hZm t).aemeasurable (hZ t ht)
  have hZpc : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Zp t ω) (Set.Icc 0 S.T) :=
    hπ.quasiMeasurePreserving.ae hZc
  have hZpm : ∀ t, Measurable (Zp t) := fun t => (hZm t).comp hπ.measurable
  have hRpc : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Rp t ω) (Set.Icc 0 S.T) := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hZc, hπ.quasiMeasurePreserving.ae hΞc] with ω hz hξ
    have h1 : ContinuousOn (fun t => flucProc m σ X₁ (S.ρ N) t (π ω)) (Set.Icc 0 S.T) :=
      continuousOn_iff_continuous_restrict.2 hξ
    have h2 : ContinuousOn (fun t : ℝ => EV.VE t 0 (EV.j (X₀ ω))) (Set.Icc 0 S.T) := by
      have hcE := hEV.maxHyp.1.cont_E (EV.j (X₀ ω))
      refine hcE.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ?_
      exact ⟨le_rfl, ht.1, ht.2⟩
    exact (h1.sub h2).sub hz
  have hRpm : ∀ t, Measurable (Rp t) := fun t =>
    (((hflucm m hmm t).comp hπ.measurable).sub
      ((EV.VE t 0).continuous.measurable.comp (EV.j.continuous.measurable.comp
        ((hflucm (S.γ : ℝ) hγm 0).comp hπ.measurable)))).sub (hZpm t)
  have hXform : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ω,
      Xp t ω = EV.VE t 0 (EV.j (X₀ ω)) + Zp t ω + Rp t ω := by
    intro t _ ω
    simp only [hRp]
    abel
  have hXbform : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ω, Xb t ω = EV.VE t 0 (EV.j (X₀' ω)) + Zb t ω :=
    fun _ _ _ => rfl
  -- the law of the particle path
  have hFm : AEMeasurable (windowPath 0 S.T (flucProc m σ X₁ (S.ρ N))) P₁ := by
    have e : windowPath 0 S.T (flucProc m σ X₁ (S.ρ N)) = flucPath m S.T σ X₁ (S.ρ N) :=
      funext fun ω => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) ω).symm
    rw [e]
    exact hΞm
  have hlaw1 : law (P₂ : Measure Ω₂) (windowPath 0 S.T Xp) =
      law P₁ (flucPath m S.T σ X₁ (S.ρ N)) := by
    have h1 := law_comp_mp hπ hFm
    have e : windowPath 0 S.T (flucProc m σ X₁ (S.ρ N)) = flucPath m S.T σ X₁ (S.ρ N) :=
      funext fun ω => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) ω).symm
    rw [e] at h1
    have e2 : windowPath 0 S.T Xp = fun ω' => flucPath m S.T σ X₁ (S.ρ N) (π ω') :=
      funext fun ω' => (flucPath_eq_windowPath m S.T σ X₁ (S.ρ N) (π ω')).symm
    rw [e2]
    exact h1
  -- the law of the Gaussian surrogate
  have hη'm : Measurable η' := hη'.mono (ℱ₁.le 0) le_rfl
  have hX₀'meas : Measurable X₀' := ((hη'm.const_smul (AN S N))).comp hπ.measurable
  have hGind := gf_coupling_indep hc hT (fun ω => AN S N • η' ω) (hη'.const_smul (AN S N))
  have hlaw₂ : P.map Y₀ = (P₂ : Measure Ω₂).map (fun ω' => EV.j (X₀' ω')) := by
    rw [hlaw]
    exact (law_comp_mp hπ (F := fun ω => EV.j (AN S N • η' ω))
      (EV.j.continuous.measurable.comp (hη'm.const_smul (AN S N))).aemeasurable).symm
  have hL := gf_law_identification_proof S M hMF N hN m K hm EV hEV P (P₂ : Measure Ω₂) ℱ₂ X₀' hX₀'meas Gb hGb
    hGind Zb hZb (Filter.Eventually.of_forall hZbc) hZbm Y₀ hY₀m hlaw₂ Y hY
  have hL' : law P (toPath m S.T Y) = law (P₂ : Measure Ω₂) (windowPath 0 S.T Xb) := hL
  -- the Wasserstein estimate on the second enlargement (P2)
  have hD := gf_coupling_difference hc hT
  have hSd := gf_coupling_cost_le hc hT
  have key := hwp Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d (S.γ : ℝ)) (NegSobolev d m) EV hEV.maxHyp X₀ X₀'
    (hX₀m.mono (ℱ₂.le 0) le_rfl) hX₀'meas (fun τ ω => Mart τ (π ω)) Gb hMπm hGbm Sd
    (fun r ω => cost r (π ω)) hD hSd Zp Zb Rp hZpS hZb hZpc (Filter.Eventually.of_forall hZbc) hRpc hZpm
    hZbm hRpm Xp Xb hXform hXbform
  rw [hlaw1, ← hL'] at key
  -- transfer the three terms from `Ω₂` to `Ω₁`
  have e1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p ∂P₁ :=
    lintegral_comp_mp hπ (f := fun ω => ‖flucProc (S.γ : ℝ) σ X₁ (S.ρ N) 0 ω - AN S N • η' ω‖ₑ ^ p)
      ((((hflucm (S.γ : ℝ) hγm 0).sub (hη'm.const_smul (AN S N))).enorm).pow_const p).aemeasurable
  have e2 : ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ^ p ∂(P₂ : Measure Ω₂) ≤ ∫⁻ ω, Bm ω ^ p ∂P₁ := by
    calc ∫⁻ ω, ‖windowPath 0 S.T Rp ω‖ₑ ^ p ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ω, Bm (π ω) ^ p ∂(P₂ : Measure Ω₂) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hπ.quasiMeasurePreserving.ae hRb] with ω hω
          exact ENNReal.rpow_le_rpow (windowPath_enorm_le S.T Rp ω (Bm (π ω)) hω) hp0.le
      _ = ∫⁻ ω, Bm ω ^ p ∂P₁ := lintegral_comp_mp hπ (f := fun ω => Bm ω ^ p) (hBm.pow_const p)
  have e3 : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r (π ω))) ^ (p / 2) ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P₁ :=
    lintegral_comp_mp hπ (f := fun ω => (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (cost r ω)) ^ (p / 2))
      (hcostm.pow_const (p / 2))
  refine key.trans ?_
  rw [e1, e3]
  exact add_le_add (add_le_add le_rfl (ENNReal.rpow_le_rpow e2 (div_nonneg zero_le_one hp0.le))) le_rfl

end HRS.MH.WpP
