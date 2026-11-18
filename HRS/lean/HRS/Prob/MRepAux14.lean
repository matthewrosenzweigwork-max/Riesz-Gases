import HRS.Prob.MRepAux13

/-!
# MREP, part 14: assembly of `martingale_representation`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Assembly

open Classical

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem martingale_representation_aux {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T) (𝒢 : InitialSigma ℱ)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type u) (_ : Countable ι) (B : ℝ≥0 → Ω' → ι → ℝ) (Φ : ℝ → Ω' → ι → H) (M' : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ S : ℝ, IsHSIntegrand P' ℱ' S Φ) ∧
      (∀ r ω', T < r → Φ r ω' = 0) ∧
      IsHilbertMartingaleWithCovariation P' ℱ' T (fun τ ω' => M τ (π ω')) (fun r ω' => Sg r (π ω')) ∧
      IsHilbertItoIntegral P' ℱ' B Φ M' ∧
      (∀ᵐ ω' ∂P', ∀ τ ∈ Set.Icc 0 T, M' τ ω' = M τ (π ω')) ∧
      (∀ r ∈ Set.Icc 0 T, ∀ᵐ ω' ∂P', hsCovForm (Φ r ω') = Sg r (π ω')) ∧
      (∀ᵐ ω' ∂P', ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), hsCovForm (Φ r ω') = Sg r (π ω')) := by
  obtain ⟨ι, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, u} (H := H)
  -- the exceptional null set
  have hbad : P {ω | ¬ (M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))} = 0 :=
    ae_iff.1 (hM.zero.and hM.cont)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  have hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T) := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  obtain ⟨Ct, hCt1, hCt2, hCt3, hCt4, hCt5, hCt6⟩ := exists_Ct hM e
  obtain ⟨S, hS1, hS2⟩ := exists_progressive_sqrt e Ct hCt1 hCt2
  -- the enlargement
  set ℱb : Filtration ℝ mΩ := augFiltration P ℱ with hℱb
  set P' : Measure (Ω × (ι → WienerSeq)) := P.prod (wMeasure ι) with hP'
  set ℱ' := prodFiltration P (wMeasure ι) ℱb (wFiltration ι) with hℱ'
  have hπp : MeasurePreserving (Prod.fst : Ω × (ι → WienerSeq) → Ω) P' P := measurePreserving_fst
  have hπm : ∀ s, Measurable[ℱ' s, ℱb s] (Prod.fst : Ω × (ι → WienerSeq) → Ω) := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have hcomap : ∀ τ, (ℱ τ).comap (Prod.fst : Ω × (ι → WienerSeq) → Ω) ≤ ℱ' τ := fun τ =>
    (MeasurableSpace.comap_mono (le_sup_left : ℱ τ ≤ ℱb τ)).trans
      (le_sup_of_le_left le_sup_left)
  have hℱbℱ : ∀ t, ℱ t ≤ ℱb t := fun t => le_sup_left
  set Mt : ℝ → Ω → H := regM T N M with hMt
  have hCprog' : ∀ x y, IsProgressive ℱb (fun r ω => Ct r ω x y) := fun x y =>
    IsProgressive.mono_filtration hℱbℱ (hCt2 x y)
  have hSprog' : ∀ x y, IsProgressive ℱb (fun r ω => inner ℝ (S r ω x) y) := fun x y =>
    IsProgressive.mono_filtration hℱbℱ (hS2 x y)
  have hGm : Measurable fun ω : Ω => ∫⁻ r in Set.Icc 0 T,
      ENNReal.ofReal (∑' i, Ct r ω (e i) (e i)) := by
    have hf : Measurable fun p : ℝ × Ω => ENNReal.ofReal (∑' i, Ct p.1 p.2 (e i) (e i)) :=
      ENNReal.measurable_ofReal.comp
        (Measurable.tsum fun i => isProgressive_measurable_uncurry (hCt2 (e i) (e i)))
    exact (hf.comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))
  have hA : ARData P' ℱ' e T (fun t ω' => Mt t ω'.1) (fun r ω' => Ct r ω'.1)
      (fun r ω' => S r ω'.1) (fun t ω' j => wienerPath t (ω'.2 j)) :=
    { complete := prodFiltration_complete P ℱb
      cont := fun ω' => regM_cont hT hN ω'.1
      adapted := fun t => (regM_adapted hT hM e hN hNm hN0 t).comp (hπm t)
      zero := fun t ht ω' => regM_zero hN ht ω'.1
      sq := fun t x => (regM_sq hT hN0 hM t x).comp_measurePreserving hπp
      mart := fun x => martingale_fst (regM_mart hT hM e hN hNm hN0 x)
      cov := fun x y => martingale_fst (regM_cov hT hM e hN hNm hN0 hCt2 hCt4 x y)
      wiener := isCylindricalBrownian_wiener_prod ℱb
      cross := fun x j => martingale_fst_mul_wiener (regM_mart hT hM e hN hNm hN0 x) j
      trace := fun r ω' => hCt1 r ω'.1
      sqrt := fun r ω' => hS1 r ω'.1
      Cprog := fun x y => isProgressive_comp_π hπm (hCprog' x y)
      Sprog := fun x y => isProgressive_comp_π hπm (hSprog' x y)
      Cint := hπp.quasiMeasurePreserving.ae hCt5
      Ctr := by
        show ∫⁻ ω', (fun ω => ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ω'.1
          ∂P' ≠ ∞
        rw [hπp.lintegral_comp hGm]
        exact hCt6 }
  obtain ⟨B, hB, hItoB⟩ := hA.representation
  have hle0 : 𝒢.1.comap (Prod.fst : Ω × (ι → WienerSeq) → Ω) ≤ ℱ' 0 :=
    (MeasurableSpace.comap_mono 𝒢.2).trans (hcomap 0)
  have hqmp := hπp.quasiMeasurePreserving
  have hMImm : IsHilbertMartingaleWithCovariation P' ℱ' T
      (fun τ ω' => M τ ω'.1) (fun r ω' => Sg r ω'.1) :=
    { martingale := fun x => martingale_fst (martingale_aug (hM.martingale x))
      zero := hqmp.ae hM.zero
      cont := hqmp.ae hM.cont
      sq_int := fun τ hτ => (hM.sq_int τ hτ).comp_measurePreserving hπp
      sigma_meas := fun x y => (hM.sigma_meas x y).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      sigma_adapted := fun σ x y => (hM.sigma_adapted σ x y).comp
        (Measurable.of_comap_le (hcomap σ))
      sigma_traceClass := hqmp.ae hM.sigma_traceClass
      sigma_int := MeasureTheory.Integrable.comp_fst hM.sigma_int (wMeasure ι)
      sigma_pathint := hqmp.ae hM.sigma_pathint
      sigma_entry_int := hqmp.ae hM.sigma_entry_int
      covariation := fun x y => martingale_fst (martingale_aug (hM.covariation x y)) }
  refine ⟨Ω × (ι → WienerSeq), inferInstance, P', inferInstance, Prod.fst, hπp, ℱ', ι, hι, B,
    PhiR e T (fun r ω' => S r ω'.1), (fun t ω' => Mt t ω'.1), hcomap, hB,
    indep_of_indep_of_le_left (indep_zero_cylPath hB) hle0, fun S' => hA.isHSIntegrand S',
    ?_, hMImm, hItoB, ?_, ?_, ?_⟩
  · intro r ω' hr
    funext j
    simp [PhiR, not_le.2 hr]
  · filter_upwards [hqmp.ae (measure_eq_zero_iff_ae_notMem.1 hN0)] with ω' hω' τ hτ
    exact regM_of_mem hτ hω'
  · intro r hr
    filter_upwards [hqmp.ae (hCt3 r hr)] with ω' h
    rw [hA.hsCovForm_PhiR r hr.2 ω']
    exact h
  · filter_upwards [hqmp.ae hCt4] with ω' hω'
    filter_upwards [hω', ae_restrict_mem measurableSet_Icc] with r hr hrI
    rw [hA.hsCovForm_PhiR r hrI.2 ω']
    exact hr

end Assembly

end HRS.MRep
