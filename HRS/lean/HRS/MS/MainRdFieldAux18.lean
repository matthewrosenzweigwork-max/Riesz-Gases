import HRS.MS.MainRdFieldAux17

/-!
# S.A.7, packet P9b: the Wasserstein estimates for one `N`

`sa6_core_W`: for `p ∈ {1,2}` the bound
`W_p(Law Ξ, Law(I) ∗ ν_G) ≤ ε^f_p + D^{1/2} + (E‖R‖^p)^{1/p}` with `D = covDiscrepancy` (from `hilbert_polar_coupling`,
`sa6_assembly_w1/w2`); the two statements `sa6_core_W1`, `sa6_core_W2` bound `D` and the remainder.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

section CoreW

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {e : ℕ → ℝ} {Kad K' Cp Ck m₂ Cin : ℝ} {χ : Euc d → ℝ} {εf : ℕ → ℝ}
  {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}

/-- The coupling step: `W_p(Law Ξ, Law(I) ∗ ν_G) ≤ W_p(Law Iemp, Law I) + √D + (E‖R‖^p)^{1/p}`, `p ∈ {1,2}`. -/
theorem sa6_core_W
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad) (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hCk : 0 ≤ Ck)
    (hCp : ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N' : ℕ, 2 ≤ N' → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N', Function.Injective X →
      ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ Rr : ℝ, 1 ≤ Rr →
        |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤ Cp * (cNormE χ h).toReal *
          (Rr ^ ((d : ℝ) / 2) * (smearScale d N' Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
            (HRS.Whole.withDensityReal ρ) + oNΛ d S.s C₀ Λ' N')) +
            (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / Rr ^ 2))
    (hm₂ : 0 ≤ m₂) (hm2 : PropagatedSecondMoment S R m₂)
    (hinit : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ))
    {Kk : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}
    (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern)
    (hcN : ∀ B : HNeg d (Γ : ℝ) →L[ℝ] HNeg d (Γ : ℝ),
      (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) → ‖B‖ ≤ 1 → ∀ σ ∈ Set.Icc (0 : ℝ) t,
        cNormE χ (fun z => ∑ j, inner ℝ (B (Kern j σ t z)) (Kern j σ t z)) ≤ ENNReal.ofReal Ck)
    {νG : Measure (HNeg d (Γ : ℝ))} (hνG : IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t Γ νG)
    {Ξ : (R N).Ω → HNeg d (Γ : ℝ)} (hΞm : Measurable Ξ) (hΞ : IsFluctFieldRepr S R N Γ t Ξ) :
    ∃ (Rr : (R N).Ω → HNeg d (Γ : ℝ)) (D : ℝ), 0 ≤ D ∧
      D ≤ t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂) ∧
      (∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ≤ ENNReal.ofReal (S.sigma N / 2 * max K' 0) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ)) ∧
      (wassersteinE 1 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
        wassersteinE 1 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) + ENNReal.ofReal (Real.sqrt D) +
          ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P) ∧
      (wassersteinE 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
        wassersteinE 2 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) + ENNReal.ofReal (Real.sqrt D) +
          (∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P) ^ ((1 : ℝ) / 2)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have htT : t ≤ S.T := ht.2
  have hq := sa6_qN_nonneg S N
  obtain ⟨ℱ, W', M, I', Rr, hF, hMad, hM, hIto, hI'meas0, hI'meas, hMt, hRm, hΞeq, hae, hpath⟩ :=
    sa6_decomp hS hΛ hadj he hsel hinit hN ht hinj hK hΞm hΞ
  have hlaw : law (R N).P (Iemp N t) = law (R N).P I' := Measure.map_congr hae
  have hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk := fun σ => sa6_kslice hK htT σ
  have hprob : ∀ σ : ℝ, HRS.Whole.IsProbDensity (S.ρ N (mrrClamp S.T σ)) := fun σ =>
    (hS.mean_field.solution N hN1).density _ (mrrClamp_mem hT σ)
  have hρm : Measurable (fun p : ℝ × Euc d => S.ρ N (mrrClamp S.T p.1) p.2) := mrr_rho_meas hS hN1
  have hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2) :=
    fun j => sa6_kern_meas_joint hK htT j
  have hγ := sa6_gamma hK ht.1 htT hq hkb hprob hρm hνG
  have hsb := sa6_sb_det (q := S.qN N) (hkb := hkb) (ρ := fun σ => S.ρ N (mrrClamp S.T σ))
    (hprob := hprob) hq hρm hKm
  have hD := sa6_covDiscrepancy_le hS hΛ hN ht hF hK hkb hprob hinj hCk hcN hCp hm₂ hm2 M hM
  set sb := sa6_sb Kern t Kk (S.qN N) hkb (fun σ => S.ρ N (mrrClamp S.T σ)) hprob with hsbdef
  set Zf := mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X with hZf
  have hD0 : 0 ≤ covDiscrepancy (R N).P t (fun r ω => hsCovForm (Zf r ω)) sb :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  have hWc : IsCylindricalBrownian (R N).P ℱ W' :=
    HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, eb, B, S', Sb, G, -, -, -, -, -, -, -, hGm, hGind, hGc,
    hGcov, hbound⟩ := hilbert_polar_coupling (R N).P ℱ t ht.1 ⟨ℱ 0, le_rfl⟩ W' hWc Zf
      (fun T' => sa6_Z_hs hF hK ht T') M hIto sb hsb
  obtain ⟨hγp, hγc, hγcov⟩ := hγ
  have h2 : law P' (G t) = νG := by
    haveI := hγp
    haveI := hGc.1
    refine Measure.ext_of_charFun (funext fun u => ?_)
    rw [HilbertCLTAux.charFun_centered_gaussian hGc, HilbertCLTAux.charFun_centered_gaussian hγc,
      hGcov, hγcov]
  have hle : (ℱ 0).comap π ≤ mΩ' :=
    (MeasurableSpace.comap_mono (ℱ.le 0)).trans hπ.measurable.comap_le
  let 𝒢' : SubSigma Ω' mΩ' := ⟨(ℱ 0).comap π, hle⟩
  have hIe : Measurable[𝒢'.1] (fun ω' => I' (π ω')) :=
    @Measurable.comp _ _ _ ((ℱ 0).comap π) (ℱ 0) _ _ _ hI'meas0 (comap_measurable π)
  have hRπ : AEMeasurable (fun ω' => Rr (π ω')) P' := (hRm.comp hπ.measurable).aemeasurable
  have hMπ : AEMeasurable (fun ω' => M t (π ω')) P' := (hMt.comp hπ.measurable).aemeasurable
  haveI : IsProbabilityMeasure (law (R N).P (I N t)) :=
    (Measure.isProbabilityMeasure_map_iff (hinit.meas N hN1 t ht).2.aemeasurable).2 inferInstance
  have hlawΞ : law P' (fun ω' => I' (π ω') + M t (π ω') + Rr (π ω')) = law (R N).P Ξ := by
    have : (fun ω' => I' (π ω') + M t (π ω') + Rr (π ω')) = Ξ ∘ π :=
      funext fun ω' => (hΞeq (π ω')).symm
    rw [this]
    show P'.map (Ξ ∘ π) = _
    rw [← Measure.map_map hΞm hπ.measurable, hπ.map_eq]
  have hlawI : law P' (fun ω' => I' (π ω')) = law (R N).P (Iemp N t) := by
    rw [hlaw]
    show P'.map (I' ∘ π) = _
    rw [← Measure.map_map hI'meas hπ.measurable, hπ.map_eq]
  have hA1 := sa6_assembly_w1 P' 𝒢' (fun ω' => I' (π ω')) (fun ω' => Rr (π ω'))
    (fun ω' => M t (π ω')) (G t) (law (R N).P (I N t)) hIe hRπ hMπ hGm hGind _ hD0 hbound
  have hA2 := sa6_assembly_w2 P' 𝒢' (fun ω' => I' (π ω')) (fun ω' => Rr (π ω'))
    (fun ω' => M t (π ω')) (G t) (law (R N).P (I N t)) hIe hRπ hMπ hGm hGind _ hD0 hbound
  have hRint : ∫⁻ ω', ‖Rr (π ω')‖ₑ ∂P' = ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P := hπ.lintegral_comp hRm.enorm
  have hRint2 : ∫⁻ ω', ‖Rr (π ω')‖ₑ ^ 2 ∂P' = ∫⁻ ζ, ‖Rr ζ‖ₑ ^ 2 ∂(R N).P :=
    hπ.lintegral_comp (hRm.enorm.pow_const 2)
  refine ⟨Rr, _, hD0, hD, hpath, ?_, ?_⟩
  · beta_reduce at hA1
    rw [hlawΞ, hlawI, h2, hRint] at hA1
    exact hA1
  · beta_reduce at hA2
    rw [hlawΞ, hlawI, h2, hRint2] at hA2
    exact hA2

end CoreW

end HRS.MS.MainRdField
