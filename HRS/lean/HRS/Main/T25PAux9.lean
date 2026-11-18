import HRS.Main.T25PAux8

/-!
# T25P, part 9: the Gaussian part of the convolution against a plain evolution (port of `GFB4Aux6/7` to `plainData V`)

`gfb4_Zb_gaussian`, `gfb4_indep_pairing` are stated for `EvolData` with `MaxHyp`; here the evolution is the plain evolution
`V` on `E_m` (`EvolData` via `Comp28.plainData`, `j = id`) with the two properties actually used: strong continuity and a norm
bound; the proofs are the same.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45

variable {d : ℕ}

theorem t25p_norm_pullback_le {m T K : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V t r‖ ≤ K) (hK : 0 ≤ K) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (ℓ : NegSobolev d m →L[ℝ] ℝ) :
    ‖pullbackVec (HRS.Uniform.Comp28.plainData V) t r ℓ‖ ≤ K * ‖ℓ‖ := by
  unfold pullbackVec
  rw [LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
  simp only [ContinuousLinearMap.comp_apply, HRS.Uniform.Comp28.plainData_VE, HRS.Uniform.Comp28.plainData_j,
    ContinuousLinearMap.id_apply]
  calc ‖ℓ (V t r b)‖ ≤ ‖ℓ‖ * ‖V t r b‖ := ℓ.le_opNorm _
    _ ≤ ‖ℓ‖ * (‖V t r‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left ((V t r).le_opNorm b) (norm_nonneg _)
    _ ≤ ‖ℓ‖ * (K * ‖b‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hVb r t hr hrt htT) (norm_nonneg _)) (norm_nonneg _)
    _ = K * ‖ℓ‖ * ‖b‖ := by ring

theorem t25p_pullback_weak {m T : ℝ} (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ℓ : NegSobolev d m →L[ℝ] ℝ) (x : NegSobolev d m) :
    ContinuousOn (fun σ => inner ℝ (pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ) x) (Set.Icc 0 t) := by
  have e : (fun σ => inner ℝ (pullbackVec (HRS.Uniform.Comp28.plainData V) t σ ℓ) x) = fun σ => ℓ (V t σ x) :=
    funext fun σ => pullback_inner (HRS.Uniform.Comp28.plainData V) t σ ℓ x
  rw [e]
  have hc := hVc x
  have hmap : Set.MapsTo (fun r : ℝ => (t, r)) (Set.Icc 0 t)
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} := fun r hr => ⟨hr.1, hr.2, ht.2⟩
  exact ℓ.continuous.comp_continuousOn (hc.comp (Continuous.continuousOn (by fun_prop)) hmap)

theorem t25p_Zb_gaussian {m T K : ℝ} (hK : 0 ≤ K) (hT0 : 0 < T)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V t r‖ ≤ K) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] {ℱ'' : Filtration ℝ mΩ'} (G : ℝ → Ω' → NegSobolev d m)
    (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, MemSobolev m (φ a)) :
    P'.map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b =>
        ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
          Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a))) (pullbackVec (HRS.Uniform.Comp28.plainData V) (ts b) σ (gfb4_ell m (φ b)))) := by
  have hT : 0 ≤ T := hT0.le
  set B : ℝ := K * ∑ b, ‖gfb4_ell m (φ b)‖ with hB
  refine gfb4_vec_gaussian hG hGc hGz hT0 ts hts (fun a σ => pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a)))
    (B := B) ?_ ?_ _ ?_ ?_
  · intro a σ hσ
    have h1 := t25p_norm_pullback_le V hVb hK hσ.1 hσ.2 (hts a).2 (gfb4_ell m (φ a))
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    exact Finset.single_le_sum (f := fun b => ‖gfb4_ell m (φ b)‖) (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  · intro a x
    exact t25p_pullback_weak V hVc (hts a) _ x
  · refine measurable_toLp_eval fun a => ?_
    exact (continuous_eval_const (hφ a)).measurable.comp (hZbm _)
  · intro a
    refine gfb4_L2_of_stochConv P' (HRS.Uniform.Comp28.plainData V) G hT (hts a).1 (hts a).2 (Zb (ts a)) (hZb _ (hts a)) (gfb4_ell m (φ a)) _ ?_
    intro ω
    simp [gfb4_ell_apply (hφ a)]

theorem t25p_indep_pairing {m T : ℝ} (hT0 : 0 < T)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P']
    {ℱ'' : Filtration ℝ mΩ'} (G G0 : ℝ → Ω' → NegSobolev d m)
    (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T G (fun r _ => Cd r))
    (hG0m : ∀ τ ∈ Set.Icc (0 : ℝ) T, Measurable (G0 τ))
    (hGG : ∀ τ ∈ Set.Icc (0 : ℝ) T, G τ =ᵐ[P'] G0 τ)
    (Zb : ℝ → Ω' → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) (Y₀' : Ω' → NegSobolev d m)
    (hind : Indep (MeasurableSpace.comap Y₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T, MeasurableSpace.comap (G0 τ) inferInstance) P')
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, MemSobolev m (φ a)) :
    IndepFun (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a) :
      EuclideanSpace ℝ (Fin p))) Y₀' P' := by
  have hT : 0 ≤ T := hT0.le
  set ys : Fin p → ℝ → NegSobolev d m := fun a σ => pullbackVec (HRS.Uniform.Comp28.plainData V) (ts a) σ (gfb4_ell m (φ a)) with hys
  set X : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a => NegSobolev.eval (Zb (ts a) ω) (φ a)
    with hX
  have hXm : Measurable X := measurable_toLp_eval fun a =>
    (continuous_eval_const (hφ a)).measurable.comp (hZbm _)
  set XN : ℕ → Ω' → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G σ ω) (ys a) T (ts a) N with hXN
  have hXNm : ∀ N, Measurable (XN N) := fun N =>
    measurable_toLp_eval fun a => measurable_isum hG (ys a) (ts a) N
  have hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P')
      atTop (𝓝 0) := by
    intro a
    refine gfb4_L2_of_stochConv P' (HRS.Uniform.Comp28.plainData V) G hT (hts a).1 (hts a).2 (Zb (ts a)) (hZb _ (hts a))
      (gfb4_ell m (φ a)) _ ?_
    intro ω
    simp [hX, gfb4_ell_apply (hφ a)]
  obtain ⟨ns, hns, hae⟩ := gfb4_subseq_ae P' hXNm hXm hL2
  -- the σ-algebra generated by the original process
  set 𝒢 : MeasurableSpace Ω' := ⨆ τ ∈ Set.Icc (0 : ℝ) T, MeasurableSpace.comap (G0 τ) inferInstance with h𝒢
  have h𝒢le : 𝒢 ≤ mΩ' := iSup₂_le fun τ hτ => (hG0m τ hτ).comap_le
  have hG0𝒢 : ∀ τ ∈ Set.Icc (0 : ℝ) T, @Measurable Ω' _ 𝒢 _ (G0 τ) := fun τ hτ =>
    (comap_measurable (G0 τ)).mono (le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) T) =>
      MeasurableSpace.comap (G0 τ) inferInstance) τ hτ) le_rfl
  set XN0 : ℕ → Ω' → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G0 σ ω) (ys a) T (ts a) N with hXN0
  have hXN0𝒢 : ∀ N, @Measurable Ω' _ 𝒢 _ (XN0 N) := fun N =>
    @measurable_toLp_eval p Ω' 𝒢 _ fun a =>
      @gfb4_isum_measurable Ω' 𝒢 _ _ _ _ _ _ _ G0 T hT hG0𝒢 (ys a) (ts a) (hts a) N
  set L : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => limUnder atTop (fun k => XN0 (ns k) ω) with hL
  have hL𝒢 : @Measurable Ω' _ 𝒢 _ L :=
    @gfb4_limUnder_meas Ω' 𝒢 p (fun k => XN0 (ns k)) (fun k => hXN0𝒢 (ns k))
  have hXL : X =ᵐ[P'] L := by
    have hcoord : ∀ᵐ ω ∂P', ∀ k, XN (ns k) ω = XN0 (ns k) ω := by
      refine ae_all_iff.2 fun k => ?_
      have : ∀ a : Fin p, (fun ω => isum (fun σ => G σ ω) (ys a) T (ts a) (ns k)) =ᵐ[P']
          fun ω => isum (fun σ => G0 σ ω) (ys a) T (ts a) (ns k) := fun a =>
        gfb4_isum_ae_eq P' hT hGG (ys a) (hts a) (ns k)
      have h2 := ae_all_iff.2 this
      filter_upwards [h2] with ω hω
      ext a
      exact hω a
    filter_upwards [hae, hcoord] with ω h1 h2
    have h3 : Tendsto (fun k => XN0 (ns k) ω) atTop (𝓝 (X ω)) := by
      refine h1.congr fun k => h2 k
    exact (h3.limUnder_eq).symm
  have hLind : IndepFun L Y₀' P' := by
    have := indep_of_indep_of_le_left hind.symm (@Measurable.comap_le Ω' _ 𝒢 _ L hL𝒢)
    exact this
  exact hLind.congr hXL.symm (Filter.EventuallyEq.refl _ _)

end HRS.T25P
