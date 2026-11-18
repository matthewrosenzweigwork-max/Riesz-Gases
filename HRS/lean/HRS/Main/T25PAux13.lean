import HRS.Main.T25PAux12
import HRS.Main.GFB1Aux2
import HRS.Main.GFSpec5
import HRS.Main.GFSpec4

/-!
# T25P, part 13: the abstract stage-2 comparison on a window (smooth and `W_p`, `p = 1, 2`)

On a probability space `Ω₁` carrying the `E_m`-valued particle data (`X₀`, `X₀'` initial, the martingale `Mart` with covariation
`Sg`, the convolution `Z`, a remainder `Rr` with a pathwise bound `Bm`, `Xp = V X₀ + Z + Rr`) and a deterministic covariation
density `Cb`, the second enlargement of the adapted Gaussian coupling (`relative_covariance_coupling_proof`) carries a Gaussian
martingale `Gb` whose convolution `Zb` gives the surrogate `V X₀' + Zb`; the target law `Λ` is assumed to be the law of this
surrogate for every realisation (`hid`).  Then `comparison_smooth_proof` and the window estimate `t25p_wass_core` (with the
measurable maximal estimate) bound the distance between `Law(Xp window)` and `Λ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q45 HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Comp28

variable {d : ℕ}

/-- The evolution package at level `m`: plain evolution, decay, the measurable maximal estimate on windows of length `T`, and
the existence of the stochastic convolution (with a.e. measurable sections and continuous paths). -/
structure T25Ev (m K c T Cmax : ℝ) (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) : Prop where
  plain : ∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution V T'
  decay : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖V t u‖ ≤ K * Real.exp (-c * (t - u))
  maxM : MaxWindowsM V T Cmax
  exists_conv : ∀ T' : ℝ, 0 < T' → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → NegSobolev d m)
    (Sg : ℝ → Ω → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)),
    IsHilbertMartingaleWithCovariation P ℱ T' M Sg →
    ∃ Z : ℝ → Ω → NegSobolev d m,
      (∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P V (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T')) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T', AEMeasurable (Z t) P)

set_option maxHeartbeats 1600000 in
theorem t25p_stage2 {m K c T Cmax : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 < T)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hEv : T25Ev m K c T Cmax V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      ∀ (Ω₁ : Type) [mΩ₁ : MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
        (ℱ₁ : Filtration ℝ mΩ₁) (X₀ X₀' : Ω₁ → NegSobolev d m),
        Measurable[ℱ₁ 0] X₀ → Measurable[ℱ₁ 0] X₀' →
        ∀ (Mart : ℝ → Ω₁ → NegSobolev d m)
          (Sg : ℝ → Ω₁ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)),
          IsHilbertMartingaleWithCovariation P₁ ℱ₁ (a + T) Mart Sg →
          ∀ (Cb : ℝ → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)), IsDetCovDensity (a + T) Cb →
          (∀ r : ℝ, a + T < r → Cb r = 0) →
          ∀ (Z Rr Xp : ℝ → Ω₁ → NegSobolev d m),
            (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
              IsStochConv P₁ V (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Z t)) →
            (∀ᵐ ω ∂P₁, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) → (∀ t, Measurable (Z t)) →
            (∀ᵐ ω ∂P₁, ContinuousOn (fun t => Rr t ω) (Set.Icc 0 (a + T))) → (∀ t, Measurable (Rr t)) →
            (∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xp t ω = V t 0 (X₀ ω) + Z t ω + Rr t ω) →
            ∀ (Bm : Ω₁ → ℝ≥0∞), AEMeasurable Bm P₁ →
            (∀ᵐ ω ∂P₁, ∀ t ∈ Set.Icc a (a + T), ‖Rr t ω‖ₑ ≤ Bm ω) →
            ∀ (Λ : Measure (PathSp T (NegSobolev d m))),
              (∀ (Ω₂ : Type) [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
                (ℱ₂ : Filtration ℝ mΩ₂) (ξ : Ω₂ → NegSobolev d m) (G : ℝ → Ω₂ → NegSobolev d m),
                Measurable ξ →
                IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) G (fun r _ => Cb r) →
                Indep (MeasurableSpace.comap ξ inferInstance)
                  (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G τ) inferInstance) P₂ →
                P₂.map ξ = P₁.map X₀' →
                ∀ Zb : ℝ → Ω₂ → NegSobolev d m,
                  (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
                    IsStochConv P₂ V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t)) →
                  (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
                  (∀ t, Measurable (Zb t)) →
                  Λ = law P₂ (windowPath a T (fun t ω => V t 0 (ξ ω) + Zb t ω))) →
              (ENNReal.ofReal (smoothDist 2 (law P₁ (windowPath a T Xp)) Λ) ≤
                ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P₁ +
                  ∫⁻ ω, Bm ω ∂P₁ +
                  ENNReal.ofReal (K ^ 2 / 2) * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
                    ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P₁) ∧
              (∀ p : ℝ, (p = 1 ∨ p = 2) →
                wassersteinE p (law P₁ (windowPath a T Xp)) Λ ≤
                  ENNReal.ofReal ((2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) * Real.exp (-c * a)) *
                      (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P₁) ^ (1 / p) +
                    (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) +
                    ENNReal.ofReal (2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) *
                      (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
                        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P₁) ^
                        (1 / 2 : ℝ)) := by
  classical
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
  have hMart2 := hcoup.martingale S hS0 (le_refl _)
  have hGaussian := hcoup.gaussian S hS0 (le_refl _)
  have hDiff := hcoup.difference S hS0 (le_refl _)
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
  have hπ0 : Measurable[ℱ₂ 0, ℱ₁ 0] π := Measurable.of_comap_le (hcoup.filtration 0)
  have hX₀2 : Measurable[ℱ₂ 0] (fun ω => X₀ (π ω)) := hX₀.comp hπ0
  have hX₀'2 : Measurable[ℱ₂ 0] (fun ω => X₀' (π ω)) := hX₀'.comp hπ0
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
  -- the trace integral
  have hFm : Measurable fun q : ℝ × Ω₁ => ENNReal.ofReal (Real.exp (-c * max (a - q.1) 0) ^ 2 *
      traceNormForm (Sg q.1 q.2 - Cb q.1)) := by
    have h1 := measurable_discrepancy_density P₁ hM hCb
    have hg : Continuous fun r : ℝ => Real.exp (-c * max (a - r) 0) ^ 2 :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((continuous_const.sub continuous_id).max continuous_const))).pow 2
    have h2 : Measurable fun q : ℝ × Ω₁ => Real.exp (-c * max (a - q.1) 0) ^ 2 :=
      hg.measurable.comp measurable_fst
    exact (h2.mul h1).ennreal_ofReal
  have hFi : Measurable fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
      (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r)) :=
    hFm.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0 : ℝ) S))
  have hiii := hπ.lintegral_comp (f := fun ω => ∫⁻ r in Set.Icc (0 : ℝ) S, ENNReal.ofReal
      (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) hFi
  have hi : ∀ p : ℝ, ∫⁻ ω', ‖X₀ (π ω') - X₀' (π ω')‖ₑ ^ p ∂(P₂ : Measure Ω₂) =
      ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P₁ := fun p =>
    hπ.lintegral_comp (f := fun ω => ‖X₀ ω - X₀' ω‖ₑ ^ p) ((hX₀m.sub hX₀'m).enorm.pow_const p)
  have hBint : ∀ p : ℝ, ∫⁻ ω', Bm (π ω') ^ p ∂(P₂ : Measure Ω₂) = ∫⁻ ω, Bm ω ^ p ∂P₁ := fun p =>
    lintegral_comp_mp hπ (f := fun ω => Bm ω ^ p) (hBm.pow_const p)
  have hB1 : ∫⁻ ω', Bm (π ω') ∂(P₂ : Measure Ω₂) = ∫⁻ ω, Bm ω ∂P₁ :=
    lintegral_comp_mp hπ hBm
  -- the smooth comparison
  have hsmooth := comparison_smooth_proof K c hK hc a T ha hT.le Ω₂ (P₂ : Measure Ω₂) ℱ₂ (NegSobolev d m) V hVe hVb
    (fun ω => X₀ (π ω)) (fun ω => X₀' (π ω)) hX₀2 hX₀'2 (fun τ ω => Mart τ (π ω)) (fun r ω => Sg r (π ω))
    hMart2 Gb Cb hCb hGb (fun t ω => Z t (π ω)) Zb (fun t ω => Rr t (π ω)) hZ1 hZb hZ2c
    (Filter.Eventually.of_forall hZbc) hR2c hZ2m hZbm hR2m (fun t ω => Xp t (π ω))
    (fun t ω => V t 0 (X₀' (π ω)) + Zb t ω) hXd2 (fun _ _ _ => rfl)
  have hi1 : ∫⁻ ω', ‖X₀ (π ω') - X₀' (π ω')‖ₑ ∂(P₂ : Measure Ω₂) = ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P₁ :=
    hπ.lintegral_comp (f := fun ω => ‖X₀ ω - X₀' ω‖ₑ) ((hX₀m.sub hX₀'m).enorm)
  have hRint1 : ∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ∂(P₂ : Measure Ω₂) ≤ ∫⁻ ω, Bm ω ∂P₁ := by
    calc ∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ∂(P₂ : Measure Ω₂)
        ≤ ∫⁻ ω', Bm (π ω') ∂(P₂ : Measure Ω₂) := lintegral_mono_ae hRwin
      _ = ∫⁻ ω, Bm ω ∂P₁ := hB1
  refine ⟨?_, ?_⟩
  · have h := hsmooth
    rw [← e1, ← hΛ] at h
    refine h.trans ?_
    refine add_le_add (add_le_add (le_of_eq ?_) hRint1) (le_of_eq ?_)
    · rw [hi1]
    · rw [hiii]
  · intro p hp
    have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
    -- the `W_p` comparison
    have hcost : ∀ᵐ ω' ∂(P₂ : Measure Ω₂), ∀ r : ℝ, 0 ≤ r → r ≤ S →
        traceNormForm (if r ≤ S then Sd r ω' else 0) ≤ traceNormForm (Sg r (π ω') - Cb r) := by
      filter_upwards [hcoup.cost, hπ.quasiMeasurePreserving.ae hM.sigma_traceClass] with ω' h htc r hr0 hrS
      rw [if_pos hrS, h r hr0 (ENNReal.ofReal_le_ofReal hrS)]
      exact bures2_le_traceNorm_any _ _ (htc r ⟨hr0, hrS⟩) (hCb.traceClass r ⟨hr0, hrS⟩)
    have hZdiff : ∀ t ∈ Set.Icc (0 : ℝ) S,
        IsStochConv (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m))
          (fun τ ω' => Mart (min τ S) (π ω') - Gb (min τ S) ω') 0 t
          (fun ω' => Z t (π ω') - Zb t ω') := fun t ht =>
      gfb4_isStochConv_sub (P₂ : Measure Ω₂) V (ContinuousLinearMap.id ℝ (NegSobolev d m))
        (fun τ => (hMm τ).comp hmπ) hGbm ht.1 ht.2 ((hZm t).comp hmπ) (hZbm t) (hZ1 t ht) (hZb t ht)
    have hcore := t25p_wass_core (K := K) (c := c) (T := T) (Cmax := Cmax) (a := a) hK hc hT.le ha hp V hVe hVb
      hEv.maxM (P₂ : Measure Ω₂) ℱ₂ (fun ω' => X₀ (π ω')) (fun ω' => X₀' (π ω')) (hX₀m.comp hmπ)
      (hX₀'m.comp hmπ) (fun τ ω' => Mart (min τ S) (π ω') - Gb (min τ S) ω')
      (fun r ω' => if r ≤ S then Sd r ω' else 0) hDiff
      (fun r ω' => traceNormForm (Sg r (π ω') - Cb r)) hcost
      (fun t ω' => Z t (π ω')) Zb (fun t ω' => Rr t (π ω')) hZdiff hZ2c (Filter.Eventually.of_forall hZbc)
      hR2c hZ2m hZbm hR2m (fun t ω' => Xp t (π ω')) (fun t ω' => V t 0 (X₀' (π ω')) + Zb t ω')
      hXd2 (fun _ _ _ => rfl)
    rw [← e1, ← hΛ] at hcore
    refine hcore.trans ?_
    have hRp : (∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ^ p ∂(P₂ : Measure Ω₂)) ^ (1 / p) ≤
        (∫⁻ ω, Bm ω ^ p ∂P₁) ^ (1 / p) := by
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      calc ∫⁻ ω', ‖windowPath a T (fun t ω => Rr t (π ω)) ω'‖ₑ ^ p ∂(P₂ : Measure Ω₂)
          ≤ ∫⁻ ω', Bm (π ω') ^ p ∂(P₂ : Measure Ω₂) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hRwin] with ω' hω'
            exact ENNReal.rpow_le_rpow hω' hp0.le
        _ = ∫⁻ ω, Bm ω ^ p ∂P₁ := hBint p
    rw [hi p]
    refine add_le_add (add_le_add le_rfl hRp) (le_of_eq ?_)
    rw [hiii]

end HRS.T25P
