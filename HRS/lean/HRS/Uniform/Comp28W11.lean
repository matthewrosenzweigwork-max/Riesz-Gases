import HRS.Uniform.Comp28W10

/-!
# COMP-28, Wasserstein part, W11: Proposition 3.28, the Wasserstein assertion

Assembly: the adapted Gaussian coupling `(Ω', π, Gb, Sd)` of Lemma 3.29, the uniqueness in law of the Gaussian convolution
(`transfer_conv`) giving a convolution `Z'` of `Gb` with the law of `Xb`, and the single-space estimate `wass_core` for the
coupling `(X∘π, V(·,0)X₀'∘π + Z')`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c HRS.GF HRS.Uniform.Q07c

universe u

section Transport

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Pullback of a stochastic convolution along a measure-preserving map. -/
lemma isStochConv_comp {P' : Measure Ω'} {P : Measure Ω} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    (V : ℝ → ℝ → H →L[ℝ] H) {M : ℝ → Ω → H} (hM : ∀ t, Measurable (M t)) {t : ℝ} {Z : Ω → H}
    (hZ : Measurable Z) (h : IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t Z) :
    IsStochConv P' V (ContinuousLinearMap.id ℝ H) (fun τ ω' => M τ (π ω')) 0 t (fun ω' => Z (π ω')) := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have h1 := hh n r h0 hn hmono hmesh
  have hm : Measurable fun ω => ‖Z ω - riemannSum V (ContinuousLinearMap.id ℝ H) M t r ω‖ₑ ^ 2 :=
    ((hZ.sub (gfb4_rs_measurable V (ContinuousLinearMap.id ℝ H) hM t r)).enorm).pow_const 2
  have e := hπ.lintegral_comp hm
  simp only [riemannSum] at e h1 ⊢
  rw [e]
  exact h1

/-- Change of variables for a measure-preserving map and an a.e.-measurable integrand. -/
lemma lintegral_comp_ae {μ : Measure Ω'} {ν : Measure Ω} {π : Ω' → Ω} (hπ : MeasurePreserving π μ ν)
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f ν) : ∫⁻ ω', f (π ω') ∂μ = ∫⁻ ω, f ω ∂ν := by
  have hf' : AEMeasurable f (μ.map π) := by rw [hπ.map_eq]; exact hf
  have := lintegral_map' hf' hπ.measurable.aemeasurable
  rw [hπ.map_eq] at this
  exact this.symm

variable {P : Measure Ω} {a T : ℝ}

/-- The law of the window path is the restriction of the law of the full path. -/
lemma law_wp_eq_map_res [IsProbabilityMeasure P] (ha : 0 ≤ a) (hT : 0 ≤ T) (Y : ℝ → Ω → H)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    law P (windowPath a T Y) = (law P (windowPath 0 (a + T) Y)).map (resWin a T ha hT) := by
  have h0 : AEMeasurable (windowPath 0 (a + T) Y) P :=
    gfb4_aemeasurable_windowPath P (by linarith) Y hY hc
  unfold law
  rw [AEMeasurable.map_map_of_aemeasurable (resWin a T ha hT).continuous.measurable.aemeasurable h0]
  refine Measure.map_congr ?_
  filter_upwards [hc] with ω hω
  exact windowPath_eq_resWin ha hT Y hω

end Transport

section Main

open HRS.Uniform.Q07c

/-- Proposition 3.28, the Wasserstein assertion (relocated statement, constant `C = 2(K² + √Cmax) + K + 1`). -/
theorem wasserstein_main (K c T Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 ≤ T) (p : ℝ)
    (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
    ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ)
      (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
      (V : ℝ → ℝ → H →L[ℝ] H) (_ : IsPlainEvolution V (a + T))
      (_ : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
      (_ : MaxWindows.{u, _} V T Cmax)
      (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
      {κ : Type} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (_ : IsCylindricalBrownian P ℱ W)
      (Φ : ℝ → Ω → κ → H) (_ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' Φ)
      (M : ℝ → Ω → H) (_ : IsHilbertItoIntegral P ℱ W Φ M)
      (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity (a + T) Cb)
      (_ : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
      (Z Zb R : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
      (X Xb : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω),
      wassersteinE p (law P (windowPath a T X)) (law P (windowPath a T Xb)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
              (Real.exp (-c * max (a - r) 0) ^ 2 *
                traceNormForm (hsCovForm (Φ r ω) - Cb r))) ∂P) ^ (1 / 2 : ℝ) := by
  classical
  have hsq0 := Real.sqrt_nonneg Cmax
  refine ⟨2 * (K ^ 2 + Real.sqrt Cmax) + K + 1, by positivity, ?_⟩
  intro a ha Ω mΩ P _ ℱ H _ _ _ _ _ _ V hVe hVb hmax X₀ X₀' hX₀ hX₀' κ _ W hW Φ hΦ M hM G Cb hCb hG
    Z Zb R hZ hZb hZc hZbc hRc hZm hZbm hRm X Xb hXd hXbd
  have hS0 : 0 ≤ a + T := by linarith
  have hHM := isHM_of_hilbertIto hW hΦ hM (a + T)
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, hcoup⟩ := relative_covariance_coupling_proof P ℱ (a + T) hS0
    ⟨ℱ 0, le_rfl⟩ M (fun r ω => hsCovForm (Φ r ω)) hHM Cb hCb
  haveI : IsProbabilityMeasure (P' : Measure Ω') := inferInstance
  have hpres : MeasurePreserving π (P' : Measure Ω') P := hcoup.preserving
  have hmπ : Measurable π := hpres.measurable
  have hMm : ∀ t, Measurable (M t) := fun t => measurable_of_isHM hHM t
  have hGaussian := hcoup.gaussian (a + T) hS0 (le_refl _)
  have hDiff := hcoup.difference (a + T) hS0 (le_refl _)
  have hMart := hcoup.martingale (a + T) hS0 (le_refl _)
  -- the Gaussian convolution on the enlargement
  have hπ0 : Measurable[ℱ' 0, ℱ 0] π := Measurable.of_comap_le (hcoup.filtration 0)
  have hξ' : Measurable[ℱ' 0] (fun ω' => X₀' (π ω')) := hX₀'.comp hπ0
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hlaw : P.map X₀' = (P' : Measure Ω').map (fun ω' => X₀' (π ω')) := by
    rw [← hpres.map_eq]
    exact Measure.map_map hX₀'m hmπ
  have hBd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ‖V t 0‖ ≤ K := by
    intro t ht
    refine (hVb 0 t le_rfl ht.1 ht.2).trans ?_
    have : Real.exp (-c * (t - 0)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht.1]
    calc K * Real.exp (-c * (t - 0)) ≤ K * 1 := mul_le_mul_of_nonneg_left this hK
      _ = K := mul_one K
  obtain ⟨Z', hZ'm, hZ'c, hZ'S, hlawZ⟩ := transfer_conv (P := P) (P' := (P' : Measure Ω')) hS0 hG
    hGaussian
    (fun r hr => if_pos (ENNReal.ofReal_le_ofReal hr.2)) V hVe.2.2 hBd hZbm hZbc hZb hX₀' hξ' hlaw
  -- the data on the enlargement
  set S : ℝ := a + T with hS
  set Dd : ℝ → Ω' → H := fun τ ω' => M (min τ S) (π ω') - Gb (min τ S) ω' with hDd_def
  have hGbm : ∀ t, Measurable (Gb t) := fun t => measurable_of_isHM hGaussian t
  have hZ1 : ∀ t ∈ Set.Icc (0 : ℝ) S,
      IsStochConv (P' : Measure Ω') V (ContinuousLinearMap.id ℝ H) (fun τ ω' => M τ (π ω')) 0 t
        (fun ω' => Z t (π ω')) := fun t ht =>
    isStochConv_comp hpres V hMm (hZm t) (hZ t ht)
  have hZdiff : ∀ t ∈ Set.Icc (0 : ℝ) S,
      IsStochConv (P' : Measure Ω') V (ContinuousLinearMap.id ℝ H) Dd 0 t
        (fun ω' => Z t (π ω') - Z' t ω') := fun t ht =>
    gfb4_isStochConv_sub (P' : Measure Ω') V (ContinuousLinearMap.id ℝ H)
      (fun τ => (hMm τ).comp hmπ) hGbm ht.1 ht.2 ((hZm t).comp hmπ) (hZ'm t) (hZ1 t ht) (hZ'S t ht)
  have hcost : ∀ᵐ ω' ∂(P' : Measure Ω'), ∀ r : ℝ, 0 ≤ r → r ≤ S →
      traceNormForm (if r ≤ S then Sd r ω' else 0) ≤
        traceNormForm (hsCovForm (Φ r (π ω')) - Cb r) := by
    filter_upwards [hcoup.cost] with ω' h r hr0 hrS
    rw [if_pos hrS, h r hr0 (ENNReal.ofReal_le_ofReal hrS)]
    exact bures2_le_traceNorm_any _ _ (isTraceClassCov_hsCovForm ((hΦ 0).summable r (π ω')))
      (hCb.traceClass r ⟨hr0, hrS⟩)
  have hcore := wass_core (K := K) (c := c) (T := T) (Cmax := Cmax) (a := a) hK hc hT ha hp V hVe hVb hmax
    (P' : Measure Ω') ℱ' (fun ω' => X₀ (π ω')) (fun ω' => X₀' (π ω')) (hX₀m.comp hmπ) (hX₀'m.comp hmπ)
    Dd (fun r ω' => if r ≤ S then Sd r ω' else 0) hDiff
    (fun r ω' => traceNormForm (hsCovForm (Φ r (π ω')) - Cb r)) hcost
    (fun t ω' => Z t (π ω')) Z' (fun t ω' => R t (π ω')) hZdiff
    (hpres.quasiMeasurePreserving.ae hZc) (ae_of_all _ hZ'c) (hpres.quasiMeasurePreserving.ae hRc)
    (fun t => (hZm t).comp hmπ) hZ'm (fun t => (hRm t).comp hmπ)
    (fun t ω' => X t (π ω')) (fun t ω' => V t 0 (X₀' (π ω')) + Z' t ω')
    (fun t ht ω' => hXd t ht (π ω')) (fun t ht ω' => rfl)
  -- transport of the laws
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) S, Measurable (X t) := fun t ht => by
    have : X t = fun ω => V t 0 (X₀ ω) + Z t ω + R t ω := funext (hXd t ht)
    rw [this]
    exact (((V t 0).continuous.measurable.comp hX₀m).add (hZm t)).add (hRm t)
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 S) := fun x =>
    continuousOn_V_zero V hVe.2.2 x
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 S) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hwX : AEMeasurable (windowPath a T X) P := aem_wp_a P ha hT X hXm hXc
  have hwR : AEMeasurable (windowPath a T R) P := aem_wp_a P ha hT R (fun t _ => hRm t) hRc
  have e1 : law P (windowPath a T X) =
      law (P' : Measure Ω') (windowPath a T (fun t ω' => X t (π ω'))) := by
    have h : AEMeasurable (windowPath a T X) ((P' : Measure Ω').map π) := by
      rw [hpres.map_eq]; exact hwX
    calc law P (windowPath a T X) = ((P' : Measure Ω').map π).map (windowPath a T X) := by
          rw [hpres.map_eq]
      _ = (P' : Measure Ω').map (windowPath a T X ∘ π) :=
          AEMeasurable.map_map_of_aemeasurable h hmπ.aemeasurable
      _ = _ := rfl
  set Yh : ℝ → Ω → H := fun t ω => V t 0 (X₀' ω) + Zb t ω with hYh
  set Yh' : ℝ → Ω' → H := fun t ω' => V t 0 (X₀' (π ω')) + Z' t ω' with hYh'
  have hYhm : ∀ t ∈ Set.Icc (0 : ℝ) S, Measurable (Yh t) := fun t _ =>
    ((V t 0).continuous.measurable.comp hX₀'m).add (hZbm t)
  have hYhc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Yh t ω) (Set.Icc 0 S) := by
    filter_upwards [hZbc] with ω h1
    exact (hVc (X₀' ω)).add h1
  have hYhm' : ∀ t ∈ Set.Icc (0 : ℝ) S, Measurable (Yh' t) := fun t _ =>
    ((V t 0).continuous.measurable.comp (hX₀'m.comp hmπ)).add (hZ'm t)
  have hYhc' : ∀ᵐ ω' ∂(P' : Measure Ω'), ContinuousOn (fun t => Yh' t ω') (Set.Icc 0 S) :=
    ae_of_all _ fun ω' => (hVc (X₀' (π ω'))).add (hZ'c ω')
  have e2 : law P (windowPath a T Xb) = law (P' : Measure Ω') (windowPath a T Yh') := by
    have hXb_eq : windowPath a T Xb = windowPath a T Yh := funext fun ω =>
      windowPath_congr_a fun t ht => hXbd (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ ω
    rw [hXb_eq, law_wp_eq_map_res ha hT Yh hYhm hYhc,
      law_wp_eq_map_res (P := (P' : Measure Ω')) ha hT Yh' hYhm' hYhc', hlawZ]
  -- the right-hand side
  have hi : ∫⁻ ω', ‖X₀ (π ω') - X₀' (π ω')‖ₑ ^ p ∂(P' : Measure Ω') =
      ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P :=
    hpres.lintegral_comp (f := fun ω => ‖X₀ ω - X₀' ω‖ₑ ^ p) ((hX₀m.sub hX₀'m).enorm.pow_const p)
  have hii : ∫⁻ ω', ‖windowPath a T (fun t ω' => R t (π ω')) ω'‖ₑ ^ p ∂(P' : Measure Ω') =
      ∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P :=
    lintegral_comp_ae hpres (f := fun ω => ‖windowPath a T R ω‖ₑ ^ p) (hwR.enorm.pow_const p)
  have hF : Measurable fun q : ℝ × Ω => ENNReal.ofReal (Real.exp (-c * max (a - q.1) 0) ^ 2 *
      traceNormForm (hsCovForm (Φ q.1 q.2) - Cb q.1)) := by
    have h1 := measurable_discrepancy_density P hHM hCb
    have hg : Continuous fun r : ℝ => Real.exp (-c * max (a - r) 0) ^ 2 :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((continuous_const.sub continuous_id).max continuous_const))).pow 2
    have h2 : Measurable fun q : ℝ × Ω => Real.exp (-c * max (a - q.1) 0) ^ 2 :=
      hg.measurable.comp measurable_fst
    exact (h2.mul h1).ennreal_ofReal
  have hFi : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
      (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (hsCovForm (Φ r ω) - Cb r)) :=
    hF.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0 : ℝ) S))
  have hiii := hpres.lintegral_comp (f := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
      (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (hsCovForm (Φ r ω) - Cb r))) hFi
  rw [e1, e2]
  refine hcore.trans (le_of_eq ?_)
  rw [hi, hii]
  congr 2
  exact congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) hiii

end Main


end HRS.Uniform.Comp28
