import HRS.Uniform.Q07cAux11

/-!
# Lemma 3.29, the adapted construction (packet Q07c)

Proof of `HRS.Uniform.relative_covariance_coupling` (statement identical): martingale representation on an
enlargement `Ω'`, a further product with independent Wiener sequences, the polar family of `Sb Φ`
(`Sb = D̄^{1/2}`), the Gaussian martingale `Ḡ = ∫ Sb dB̃` and the difference integrand
`Z = Φ̂ - Sb Ψ̃`, whose trace norm is `𝔟(ΦΦ*, D̄)²` pathwise (helpers in `HRS/Uniform/Q07cAux*.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

open HRS.Uniform.Q07c

section Relative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lemma 3.29, the adapted construction (proved here; statement identical to
`relative_covariance_coupling`). -/
theorem relative_covariance_coupling_proof {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hDb : IsDetCovDensity T Db) :
    AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db (· = ·)
      (fun r ω => bures2 (Sg r ω) (Db r)) := by
  classical
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', κ, hκ, B, Φ, M', hfilt, hB, -, hΦ, hΦ0, hMimm, hM'I,
    hM'eq, -, hΦSgF⟩ := martingale_representation P ℱ T hT 𝒢 M Sg hM
  haveI := hP'
  haveI := hκ
  obtain ⟨ιe, hι, Gb, Z, hGc, hG0, hGHM, hZhs, hNHM, hcost⟩ :=
    coupling_core P' ℱ' B hB Φ hΦ M' hM'I T hT (fun r ω hr => hΦ0 r ω hr) Db hDb
  haveI := hι
  obtain ⟨ι₀, hι₀, e0, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι₀
  have hπp : MeasurePreserving (Prod.fst : Ω' × (ιe → WienerSeq) → Ω')
      (P'.prod (wMeasure ιe)) P' := measurePreserving_fst
  have hπ''p : MeasurePreserving (fun p : Ω' × (ιe → WienerSeq) => π p.1)
      (P'.prod (wMeasure ιe)) P := hπ.comp hπp
  have hfst : ∀ s, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s, ℱ' s]
      (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have hfilt'' : ∀ s, (ℱ s).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) ≤
      prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s := fun s => by
    have h1 : (ℱ s).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) =
        ((ℱ s).comap π).comap (Prod.fst : Ω' × (ιe → WienerSeq) → Ω') := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [h1]
    exact (MeasurableSpace.comap_mono (hfilt s)).trans (le_sup_of_le_left le_sup_left)
  have hπ''m : ∀ s, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) s, ℱ s]
      (fun p : Ω' × (ιe → WienerSeq) => π p.1) := fun s => Measurable.of_comap_le (hfilt'' s)
  have hcomplete : IsCompleteFiltration (P'.prod (wMeasure ιe))
      (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)) := HRS.MRep.prodFiltration_complete P' ℱ'
  have hlift := hMimm.comp_fst (ι := ιe)
  -- the difference density
  have hZtc : ∀ r p, IsTraceClassCov (hsCovForm (Z r p)) := fun r p =>
    isTraceClassCov_hsCovForm ((hZhs 0).summable r p)
  -- joint measurability and adaptedness of the ingredients of `Sd`
  have hCm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      hsCovForm (Φ a.1 a.2.1) x y := fun x y => by
    have h : Measurable fun p : ℝ × Ω' => hsCovForm (Φ p.1 p.2) x y :=
      HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hΦ x y)
    have hf : Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, a.2.1) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    exact Measurable.comp (g := fun p : ℝ × Ω' => hsCovForm (Φ p.1 p.2) x y)
      (f := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, a.2.1)) h hf
  have hZm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      hsCovForm (Z a.1 a.2) x y := fun x y =>
    HRS.MRep.isProgressive_measurable_uncurry (isProgressive_hsCov hZhs x y)
  have hSm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
      Sg a.1 (π a.2.1) x y := fun x y => by
    have h : Measurable (Function.uncurry fun σ ω => Sg σ ω x y) := hM.sigma_meas x y
    have hf : Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, π a.2.1) :=
      measurable_fst.prodMk (hπ.measurable.comp (measurable_fst.comp measurable_snd))
    exact Measurable.comp (g := Function.uncurry fun σ ω => Sg σ ω x y)
      (f := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => (a.1, π a.2.1)) h hf
  have hDm : ∀ x y : H, Measurable fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1 x y := fun x y =>
    (hDb.meas x y).comp measurable_fst
  -- the difference covariation density
  obtain ⟨Sd, hSdDef⟩ : ∃ Sd : ℝ → Ω' × (ιe → WienerSeq) → (H →L[ℝ] H →L[ℝ] ℝ), ∀ r p,
      Sd r p = SdDef e0 (fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
        (fun a => hsCovForm (Φ a.1 a.2.1)) (fun a => hsCovForm (Z a.1 a.2))
        (fun a => Sg a.1 (π a.2.1)) (r, p) := ⟨_, fun _ _ => rfl⟩
  have hSdm : ∀ x y : H, Measurable (Function.uncurry fun r p => Sd r p x y) := fun x y => by
    have h := measurable_SdDef e0 hCm hZm hSm hDm x y
    have e : (Function.uncurry fun r p => Sd r p x y) = fun a : ℝ × (Ω' × (ιe → WienerSeq)) =>
        SdDef e0 (fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
          (fun a => hsCovForm (Φ a.1 a.2.1)) (fun a => hsCovForm (Z a.1 a.2))
          (fun a => Sg a.1 (π a.2.1)) a x y := by
      funext ⟨r, p⟩; simp only [Function.uncurry_apply_pair, hSdDef]
    rw [e]; exact h
  have hSda : ∀ σ (x y : H), Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
      (fun p => Sd σ p x y) := by
    intro σ x y
    have h1 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1) x y := fun x y =>
      (adapted_hsCov hΦ σ x y).comp (hfst σ)
    have h2 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Z σ p) x y := fun x y =>
      adapted_hsCov hZhs σ x y
    have h3 : ∀ x y : H, Measurable[prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ]
        fun p : Ω' × (ιe → WienerSeq) => Sg σ (π p.1) x y := fun x y =>
      (hM.sigma_adapted σ x y).comp (hπ''m σ)
    have := measurable_SdDef (mα := prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) σ) e0
      (D := fun _ => Db σ) (C := fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1))
      (Z := fun p => hsCovForm (Z σ p)) (S := fun p => Sg σ (π p.1)) h1 h2 h3
      (fun x y => measurable_const) x y
    have e : (fun p : Ω' × (ιe → WienerSeq) => Sd σ p x y) = fun p =>
        SdDef e0 (fun _ => Db σ) (fun p : Ω' × (ιe → WienerSeq) => hsCovForm (Φ σ p.1))
          (fun p => hsCovForm (Z σ p)) (fun p => Sg σ (π p.1)) p x y := by
      funext p; rw [hSdDef]; rfl
    rw [e]; exact this
  have hSdtc : ∀ σ p, IsTraceClassCov (Sd σ p) := fun σ p => by
    rw [hSdDef]; exact SdDef_tc e0 (fun a => hZtc _ _) _
  have hgoodae : ∀ᵐ p ∂(P'.prod (wMeasure ιe)), ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      hsCovForm (Φ σ p.1) = Sg σ (π p.1) :=
    hπp.quasiMeasurePreserving.ae hΦSgF
  have hMM' : ∀ τ', τ' ≤ T → ∀ᵐ p ∂(P'.prod (wMeasure ιe)), M τ' (π p.1) = M' τ' p.1 := by
    intro τ' hτ'
    have hz' : ∀ᵐ ω ∂P', M τ' (π ω) = M' τ' ω := by
      by_cases h0 : 0 ≤ τ'
      · exact hM'eq.mono fun ω h => (h τ' ⟨h0, hτ'⟩).symm
      · have hz := isHM_ae_zero_nonpos hMimm (not_le.1 h0).le
        exact hz.mono fun ω h => by
          have h1 : M τ' (π ω) = 0 := h
          rw [h1, hM'I.zero τ' (not_le.1 h0).le ω]
    exact hπp.quasiMeasurePreserving.ae hz'
  refine ⟨Ω' × (ιe → WienerSeq), inferInstance, ⟨P'.prod (wMeasure ιe), inferInstance⟩,
    fun p => π p.1, prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe), Gb, Sd, ?_⟩
  refine ⟨hπ''p, hfilt'', ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS hST
    have hST' : S ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hST
    exact hlift.mono_congr hS hST' hlift.sigma_meas hlift.sigma_adapted (fun _ _ _ => rfl)
  · intro S hS hST
    have hST' : S ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hST
    simp only [ENNReal.ofReal_le_ofReal_iff hT]
    exact hGHM.mono_congr hS hST' hGHM.sigma_meas hGHM.sigma_adapted (fun _ _ _ => rfl)
  · intro S hS hST
    have hST' : S ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hST
    have hae : ∀ᵐ p ∂(P'.prod (wMeasure ιe)), ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) S)),
        Sd σ p = hsCovForm (Z σ p) := by
      filter_upwards [hgoodae] with p hp
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc_right hST') hp]
        with σ hσ
      rw [hSdDef]
      unfold SdDef
      simp only [hσ, if_true]
    have hst := (hNHM T).stop_congr hcomplete hS hST' hSdm hSda hSdtc hae
    refine hst.congr_process hcomplete (fun τ => ?_) (fun τ => ?_) ?_
    · exact ((measurable_of_isHM hM (min τ S)).comp hπ''p.measurable).sub
        (measurable_of_isHM hGHM (min τ S))
    · have hτ' : min τ S ≤ T := (min_le_right τ S).trans hST'
      filter_upwards [hMM' (min τ S) hτ'] with p hp
      show M (min τ S) (π p.1) - Gb (min τ S) p = M' (min (min τ S) T) p.1 - Gb (min τ S) p
      rw [hp, min_eq_left hτ']
    · filter_upwards [hπp.quasiMeasurePreserving.ae hMimm.cont] with p hp
      have h1 : ContinuousOn (fun τ => M τ (π p.1) - Gb τ p) (Set.Icc 0 S) :=
        (hp.mono (Set.Icc_subset_Icc_right hST')).sub (hGc p).continuousOn
      refine h1.congr fun τ hτ => ?_
      simp [min_eq_left hτ.2]
  · have hle : (𝒢.1).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1) ≤
        prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe) 0 :=
      (MeasurableSpace.comap_mono 𝒢.2).trans (hfilt'' 0)
    have h := indep_path hGHM hT hGc hG0
      (⟨(𝒢.1).comap (fun p : Ω' × (ιe → WienerSeq) => π p.1), hle⟩ :
        InitialSigma (prodFiltration P' (wMeasure ιe) ℱ' (wFiltration ιe)))
    have hset : {τ : ℝ | 0 ≤ τ ∧ ENNReal.ofReal τ ≤ ENNReal.ofReal T} =
        {τ : ℝ | 0 ≤ τ ∧ τ ≤ T} := by
      ext τ; simp only [Set.mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff hT]
    rw [hset]
    exact h
  · filter_upwards [hπ''p.quasiMeasurePreserving.ae hM.sigma_traceClass] with p hp r hr0 hrT
    have hrT' : r ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hrT
    have hr : r ∈ Set.Icc 0 T := ⟨hr0, hrT'⟩
    rw [hSdDef]
    exact traceNormForm_SdDef e0 (D := fun a : ℝ × (Ω' × (ιe → WienerSeq)) => Db a.1)
      (C := fun a => hsCovForm (Φ a.1 a.2.1)) (Z := fun a => hsCovForm (Z a.1 a.2))
      (S := fun a => Sg a.1 (π a.2.1)) (r, p) (hp r hr) (hDb.traceClass r hr)
      (fun h => by
        show traceNormForm (hsCovForm (Z r p)) = bures2 (Sg r (π p.1)) (Db r)
        rw [hcost r hr p]
        exact congrArg (fun F => bures2 F (Db r)) h)

example := (@relative_covariance_coupling_proof : type_of% @relative_covariance_coupling)

end Relative

end Uniform

end HRS
