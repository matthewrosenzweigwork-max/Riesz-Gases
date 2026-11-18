import HRS.ME.CritSpec
import HRS.Main.T25PAux13

/-!
# Critical stage 2: the `p = 2` Wasserstein comparison with the Bures cost (proof of `HRS.ME.Crit.crit_stage2`)

Body of `HRS.T25P.t25p_stage2` (`p = 2`, Wasserstein conclusion only) with the cost function
`fun r ω' => bures2 (Sg r (π ω')) (Cb r)` handed to `t25p_wass_core`.  The cost identity `hcoup.cost` makes `hcost`
an equality.  The Bures integral is transported from `Ω₂` to `Ω₁` through a measurable version of the integrand: the
trace-class property of `Sg` holds off a null set `N`, so the integrand agrees a.e. with a jointly measurable one built
from `measurable_bures2` (with `Sg` and `Cb` cut off outside `[0,S] × Nᶜ`, resp. `[0,S]`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritStage2

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q45 HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Comp28 HRS.T25P

theorem crit_stage2_proof {d : ℕ} : type_of% (@HRS.ME.Crit.crit_stage2 d) := by
  classical
  intro m K c T Cmax hK hc hT V hEv
  have hsq0 := Real.sqrt_nonneg Cmax
  refine ⟨2 * (K ^ 2 + Real.sqrt Cmax) + K + 1, by positivity, ?_⟩
  intro a ha Ω₁ mΩ₁ P₁ _ ℱ₁ X₀ X₀' hX₀ hX₀' Mart Sg hM Cb hCb hCb0 Z Rr Xp hZS hZc hZm hRc hRm hXd Bm hBm hbd Λ hid
  have hS0 : 0 ≤ a + T := by linarith
  have hT' : 0 < a + T := by linarith
  set S : ℝ := a + T with hS
  -- the coupling
  obtain ⟨Ω₂, mΩ₂, P₂, π, ℱ₂, Gb, Sd, hcoup⟩ := relative_covariance_coupling_proof P₁ ℱ₁ S hS0
    ⟨ℱ₁ 0, le_rfl⟩ Mart Sg hM Cb hCb
  haveI : IsProbabilityMeasure (P₂ : Measure Ω₂) := inferInstance
  have hπ : MeasurePreserving π (P₂ : Measure Ω₂) P₁ := hcoup.preserving
  have hmπ : Measurable π := hπ.measurable
  have hDiff := hcoup.difference S hS0 (le_refl _)
  have hGaussian := hcoup.gaussian S hS0 (le_refl _)
  have hGb : IsHilbertMartingaleWithCovariation (P₂ : Measure Ω₂) ℱ₂ S Gb (fun r _ => Cb r) := by
    have e : (fun (r : ℝ) (_ : Ω₂) => if ENNReal.ofReal r ≤ ENNReal.ofReal S then Cb r else 0) =
        fun r _ => Cb r := by
      funext r _
      by_cases hr : r ≤ S
      · rw [if_pos (ENNReal.ofReal_le_ofReal hr)]
      · rw [if_neg, hCb0 r (lt_of_not_ge hr)]
        intro h
        exact hr ((ENNReal.ofReal_le_ofReal_iff hS0).1 h)
    rw [e] at hGaussian
    exact hGaussian
  have hMm : ∀ t, Measurable (Mart t) := fun t => measurable_of_isHM hM t
  have hGbm : ∀ t, Measurable (Gb t) := fun t => measurable_of_isHM hGb t
  -- the convolution of `Gb`
  obtain ⟨Zb₀, hZb₀, hZbc₀, hZbm₀⟩ := hEv.exists_conv S hT' Ω₂ (P₂ : Measure Ω₂) ℱ₂ Gb (fun r _ => Cb r) hGb
  obtain ⟨Zb, hZbm, hZbc, hZbeq⟩ := gf_measurable_modification_proof (P₂ : Measure Ω₂) S Zb₀ hZbc₀ hZbm₀
  have hZb : ∀ t ∈ Set.Icc (0 : ℝ) S, IsStochConv (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m)) Gb 0 t (Zb t) :=
    fun t ht => isStochConv_congr_ae (hZb₀ t ht) (hZbeq t ht).symm
  -- data on the second enlargement
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ₁.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ₁.le 0) le_rfl
  have hZ1 : ∀ t ∈ Set.Icc (0 : ℝ) S,
      IsStochConv (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m))
        (fun τ ω' => Mart τ (π ω')) 0 t (fun ω' => Z t (π ω')) := fun t ht =>
    isStochConv_comp hπ V hMm (hZm t) (hZS t ht)
  have hZ2c : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Z t (π ω)) (Set.Icc 0 S) :=
    hπ.quasiMeasurePreserving.ae hZc
  have hR2c : ∀ᵐ ω ∂(P₂ : Measure Ω₂), ContinuousOn (fun t => Rr t (π ω)) (Set.Icc 0 S) :=
    hπ.quasiMeasurePreserving.ae hRc
  have hZ2m : ∀ t, Measurable (fun ω => Z t (π ω)) := fun t => (hZm t).comp hmπ
  have hR2m : ∀ t, Measurable (fun ω => Rr t (π ω)) := fun t => (hRm t).comp hmπ
  have hXd2 : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ ω, Xp t (π ω) = V t 0 (X₀ (π ω)) + Z t (π ω) + Rr t (π ω) :=
    fun t ht ω => hXd t ht (π ω)
  have hVe := hEv.plain S hS0
  have hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)) :=
    fun r t hr hrt _ => hEv.decay r t hr hrt
  -- measurability and continuity of `Xp`, and the window laws
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) S, Measurable (Xp t) := fun t ht => by
    have : Xp t = fun ω => V t 0 (X₀ ω) + Z t ω + Rr t ω := funext (hXd t ht)
    rw [this]
    exact (((V t 0).continuous.measurable.comp hX₀m).add (hZm t)).add (hRm t)
  have hVc : ∀ x : NegSobolev d m, ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 S) := fun x =>
    continuousOn_V_zero V hVe.2.2 x
  have hXc : ∀ᵐ ω ∂P₁, ContinuousOn (fun t => Xp t ω) (Set.Icc 0 S) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hwX : AEMeasurable (windowPath a T Xp) P₁ := aem_wp_a P₁ ha hT.le Xp hXm hXc
  have e1 : law P₁ (windowPath a T Xp) =
      law (P₂ : Measure Ω₂) (windowPath a T (fun t ω' => Xp t (π ω'))) := by
    have h : AEMeasurable (windowPath a T Xp) ((P₂ : Measure Ω₂).map π) := by
      rw [hπ.map_eq]; exact hwX
    calc law P₁ (windowPath a T Xp) = ((P₂ : Measure Ω₂).map π).map (windowPath a T Xp) := by
          rw [hπ.map_eq]
      _ = (P₂ : Measure Ω₂).map (windowPath a T Xp ∘ π) :=
          AEMeasurable.map_map_of_aemeasurable h hmπ.aemeasurable
      _ = _ := rfl
  -- the surrogate and the identification of the target law
  have hind := gf_coupling_indep hcoup hS0 (fun ω => X₀' ω) hX₀'
  have hlawξ : (P₂ : Measure Ω₂).map (fun ω => X₀' (π ω)) = P₁.map X₀' := by
    have := Measure.map_map (μ := (P₂ : Measure Ω₂)) hX₀'m hmπ
    rw [show (fun ω => X₀' (π ω)) = X₀' ∘ π from rfl, ← this, hπ.map_eq]
  have hΛ : Λ = law (P₂ : Measure Ω₂) (windowPath a T (fun t ω' => V t 0 (X₀' (π ω')) + Zb t ω')) :=
    hid Ω₂ (P₂ : Measure Ω₂) ℱ₂ (fun ω => X₀' (π ω)) Gb (hX₀'m.comp hmπ) hGb hind hlawξ Zb hZb
      (Filter.Eventually.of_forall hZbc) hZbm
  -- the window remainder bound on the second enlargement
  have hRwin : ∀ᵐ ω' ∂(P₂ : Measure Ω₂), ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ≤ Bm (π ω') := by
    filter_upwards [hπ.quasiMeasurePreserving.ae hbd] with ω' hω'
    refine wp_enorm_le_a a T (fun t ω => Rr t (π ω)) ω' (Bm (π ω')) fun t ht => ?_
    exact hω' (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hBint : ∀ p : ℝ, ∫⁻ ω', Bm (π ω') ^ p ∂(P₂ : Measure Ω₂) = ∫⁻ ω, Bm ω ^ p ∂P₁ := fun p =>
    lintegral_comp_mp hπ (f := fun ω => Bm ω ^ p) (hBm.pow_const p)
  have hi : ∫⁻ ω', ‖X₀ (π ω') - X₀' (π ω')‖ₑ ^ (2 : ℝ) ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ (2 : ℝ) ∂P₁ :=
    hπ.lintegral_comp (f := fun ω => ‖X₀ ω - X₀' ω‖ₑ ^ (2 : ℝ)) ((hX₀m.sub hX₀'m).enorm.pow_const _)
  -- the Bures integrand: a jointly measurable version off a null set
  have hgood : ∀ᵐ ω ∂P₁, ∀ σ ∈ Set.Icc (0 : ℝ) S, IsTraceClassCov (Sg σ ω) := hM.sigma_traceClass
  obtain ⟨N, hsubN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ ω, ω ∉ N → ∀ σ ∈ Set.Icc (0 : ℝ) S, IsTraceClassCov (Sg σ ω) := by
    intro ω hω
    by_contra h
    exact hω (hsubN (show ω ∈ {ω' | ¬ ∀ σ ∈ Set.Icc (0 : ℝ) S, IsTraceClassCov (Sg σ ω')} from h))
  obtain ⟨ι₀, hι₀, e0, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type (H := NegSobolev d m)
  haveI := hι₀
  have hTC0 : IsTraceClassCov (0 : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) := by
    refine ⟨fun x y => by simp, fun x => by simp, ⟨ι₀, e0, by simpa using summable_zero⟩⟩
  have hGm : MeasurableSet (Set.Icc (0 : ℝ) S ×ˢ Nᶜ) := measurableSet_Icc.prod hNm.compl
  have hTC1 : ∀ q : ℝ × Ω₁, IsTraceClassCov (if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 else 0) := by
    rintro ⟨r, ω⟩
    by_cases hq : (r, ω) ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ
    · rw [if_pos hq]
      exact hgoodN ω hq.2 r hq.1
    · rw [if_neg hq]
      exact hTC0
  have hTC2 : ∀ r : ℝ, IsTraceClassCov (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0) := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) S
    · rw [if_pos hr]; exact hCb.traceClass r hr
    · rw [if_neg hr]; exact hTC0
  have hCsm : ∀ x y : NegSobolev d m,
      Measurable fun q : ℝ × Ω₁ => (if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 else 0) x y := by
    intro x y
    have hf : Measurable fun q : ℝ × Ω₁ => Sg q.1 q.2 x y := hM.sigma_meas x y
    have e : (fun q : ℝ × Ω₁ => (if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 else 0) x y) =
        fun q => if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 x y else 0 := by
      funext q; split_ifs <;> simp
    rw [e]
    exact Measurable.ite (p := fun q : ℝ × Ω₁ => q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ) hGm hf measurable_const
  have hCb2m : ∀ x y : NegSobolev d m,
      Measurable fun r : ℝ => (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0) x y := by
    intro x y
    have e : (fun r : ℝ => (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0) x y) =
        fun r => if r ∈ Set.Icc (0 : ℝ) S then Cb r x y else 0 := by
      funext r; split_ifs <;> simp
    rw [e]
    exact Measurable.ite (p := fun r : ℝ => r ∈ Set.Icc (0 : ℝ) S) measurableSet_Icc (hCb.meas x y)
      measurable_const
  have hBures : Measurable fun q : ℝ × Ω₁ =>
      bures2 (if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 else 0)
        (if q.1 ∈ Set.Icc (0 : ℝ) S then Cb q.1 else 0) :=
    measurable_bures2 e0 hTC1 (fun q => hTC2 q.1) hCsm (fun x y => (hCb2m x y).comp measurable_fst)
  have hFmeas : Measurable fun q : ℝ × Ω₁ => ENNReal.ofReal (Real.exp (-c * max (a - q.1) 0) ^ 2 *
      bures2 (if q ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg q.1 q.2 else 0)
        (if q.1 ∈ Set.Icc (0 : ℝ) S then Cb q.1 else 0)) := by
    have hg : Continuous fun r : ℝ => Real.exp (-c * max (a - r) 0) ^ 2 :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((continuous_const.sub continuous_id).max continuous_const))).pow 2
    have h2 : Measurable fun q : ℝ × Ω₁ => Real.exp (-c * max (a - q.1) 0) ^ 2 :=
      hg.measurable.comp measurable_fst
    exact (h2.mul hBures).ennreal_ofReal
  have hFm2 : Measurable fun ω : Ω₁ => ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
      (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (if (r, ω) ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg r ω else 0)
          (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0)) :=
    hFmeas.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0 : ℝ) S))
  have hFe : ∀ᵐ ω ∂P₁, (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
        (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r ω) (Cb r))) =
      ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
        (Real.exp (-c * max (a - r) 0) ^ 2 *
          bures2 (if (r, ω) ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg r ω else 0)
            (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    refine setLIntegral_congr_fun measurableSet_Icc (fun r hr => ?_)
    have h1 : (if (r, ω) ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg r ω else 0) = Sg r ω :=
      if_pos (Set.mk_mem_prod hr hω)
    have h2 : (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0) = Cb r := if_pos hr
    simp only [h1, h2]
  have hiB : ∫⁻ ω', (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
        (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r (π ω')) (Cb r))) ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
        (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r ω) (Cb r))) ∂P₁ := by
    calc ∫⁻ ω', (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r (π ω')) (Cb r))) ∂(P₂ : Measure Ω₂)
        = ∫⁻ ω', (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 *
              bures2 (if (r, π ω') ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg r (π ω') else 0)
                (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0))) ∂(P₂ : Measure Ω₂) :=
          lintegral_congr_ae (hπ.quasiMeasurePreserving.ae hFe)
      _ = ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 *
              bures2 (if (r, ω) ∈ Set.Icc (0 : ℝ) S ×ˢ Nᶜ then Sg r ω else 0)
                (if r ∈ Set.Icc (0 : ℝ) S then Cb r else 0))) ∂P₁ :=
          hπ.lintegral_comp hFm2
      _ = ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 * bures2 (Sg r ω) (Cb r))) ∂P₁ :=
          lintegral_congr_ae (hFe.mono fun ω h => h.symm)
  -- the `W_2` comparison
  have hZdiff : ∀ t ∈ Set.Icc (0 : ℝ) S,
      IsStochConv (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m))
        (fun τ ω' => Mart (min τ S) (π ω') - Gb (min τ S) ω') 0 t
        (fun ω' => Z t (π ω') - Zb t ω') := fun t ht =>
    gfb4_isStochConv_sub (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m))
      (fun τ => (hMm τ).comp hmπ) hGbm ht.1 ht.2 ((hZm t).comp hmπ) (hZbm t) (hZ1 t ht) (hZb t ht)
  have hcost : ∀ᵐ ω' ∂(P₂ : Measure Ω₂), ∀ r : ℝ, 0 ≤ r → r ≤ S →
      traceNormForm (if r ≤ S then Sd r ω' else 0) ≤ bures2 (Sg r (π ω')) (Cb r) := by
    filter_upwards [hcoup.cost] with ω' h r hr0 hrS
    rw [if_pos hrS]
    exact le_of_eq (h r hr0 (ENNReal.ofReal_le_ofReal hrS))
  have hcore := t25p_wass_core (K := K) (c := c) (T := T) (Cmax := Cmax) (a := a) (p := 2) hK hc hT.le ha
    (Or.inr rfl) V hVe hVb hEv.maxM (P₂ : Measure Ω₂) ℱ₂ (fun ω' => X₀ (π ω')) (fun ω' => X₀' (π ω'))
    (hX₀m.comp hmπ) (hX₀'m.comp hmπ) (fun τ ω' => Mart (min τ S) (π ω') - Gb (min τ S) ω')
    (fun r ω' => if r ≤ S then Sd r ω' else 0) hDiff
    (fun r ω' => bures2 (Sg r (π ω')) (Cb r)) hcost
    (fun t ω' => Z t (π ω')) Zb (fun t ω' => Rr t (π ω')) hZdiff hZ2c (Filter.Eventually.of_forall hZbc)
    hR2c hZ2m hZbm hR2m (fun t ω' => Xp t (π ω')) (fun t ω' => V t 0 (X₀' (π ω')) + Zb t ω')
    hXd2 (fun _ _ _ => rfl)
  rw [← e1, ← hΛ] at hcore
  refine hcore.trans ?_
  have hRp : (∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ^ (2 : ℝ) ∂(P₂ : Measure Ω₂)) ^ (1 / (2 : ℝ)) ≤
      (∫⁻ ω, Bm ω ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) := by
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ^ (2 : ℝ) ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ω', Bm (π ω') ^ (2 : ℝ) ∂(P₂ : Measure Ω₂) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hRwin] with ω' hω'
          exact ENNReal.rpow_le_rpow hω' (by norm_num)
      _ = ∫⁻ ω, Bm ω ^ (2 : ℝ) ∂P₁ := hBint 2
  rw [hi, hiB]
  exact add_le_add (add_le_add le_rfl hRp) le_rfl

end HRS.ME.CritStage2
