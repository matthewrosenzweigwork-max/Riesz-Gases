import HRS.Main.A8PAux1

/-!
# Packet A8P, part 2: the abstract `W_p` comparison (Hilbert case)

`a8p_wass_abstract`: from the polar coupling of Corollary A.23 (on an enlargement), for `Z = I_emp + M_t + R`,
`W_p(Law Z, Law Ĩ * γ) ≤ (E‖I_emp - Ĩ‖^p)^{1/p} + D^{1/2} + (E‖R‖^p)^{1/p}`, `p ∈ [1,2]`, for ANY random vector `Ĩ`
(only its law enters; no `𝒢`-measurability), `γ` the centred Gaussian of covariance `∫ Σ̄`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

section Wass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Convolution with a fixed probability measure does not increase `W_p`. -/
theorem a8p_wass_conv_le (p : ℝ) (hp : 1 ≤ p) (μ ν γ : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure γ] :
    wassersteinE p (μ ∗ γ) (ν ∗ γ) ≤ wassersteinE p μ ν := by
  have hp0 : 0 < p := by linarith
  have e1 : μ ∗ γ = (μ.prod γ).map (fun z : H × H => z.1 + z.2) := rfl
  have e2 : ν ∗ γ = (ν.prod γ).map (fun z : H × H => z.1 + z.2) := rfl
  rw [e1, e2]
  refine le_iInf fun π => ?_
  obtain ⟨π, hπ⟩ := π
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hkey : ∀ (f : H × H → H), Measurable f → ∀ (ρ : Measure H), π.map f = ρ →
      ((π.prod γ).map (fun w : (H × H) × H => f w.1 + w.2)) =
        (ρ.prod γ).map (fun z : H × H => z.1 + z.2) := by
    intro f hf ρ hρ
    have e1 : (fun w : (H × H) × H => f w.1 + w.2) =
        (fun z : H × H => z.1 + z.2) ∘ (Prod.map f id) := by ext w <;> simp
    rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), ← hρ]
    congr 1
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  set T : (H × H) × H → H × H := fun w => (w.1.1 + w.2, w.1.2 + w.2) with hT
  have hTm : Measurable T := by rw [hT]; fun_prop
  have hcoup : IsCoupling ((π.prod γ).map T)
      ((μ.prod γ).map (fun z : H × H => z.1 + z.2))
      ((ν.prod γ).map (fun z : H × H => z.1 + z.2)) := by
    constructor
    · rw [Measure.map_map measurable_fst hTm]
      exact hkey Prod.fst measurable_fst _ hπ.1
    · rw [Measure.map_map measurable_snd hTm]
      exact hkey Prod.snd measurable_snd _ hπ.2
  refine (wassersteinE_le_cost hcoup).trans ?_
  refine le_of_eq ?_
  congr 1
  rw [lintegral_map (by fun_prop) hTm]
  have : ∀ w : (H × H) × H, ENNReal.ofReal (‖(T w).1 - (T w).2‖ ^ p) =
      ENNReal.ofReal (‖w.1.1 - w.1.2‖ ^ p) := fun w => by
    simp [hT]
  simp only [this]
  rw [lintegral_prod _ (by fun_prop)]
  simp


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem a8p_wass_abstract (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → H) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb)
    (γ : Measure H) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (Iemp Itil Z R : Ω → H) (hI : Measurable[ℱ 0] Iemp) (hIt : AEMeasurable Itil P)
    (hR : AEMeasurable R P) (hZ : ∀ᵐ ω ∂P, Z ω = Iemp ω + M t ω + R ω)
    (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    wassersteinE p (law P Z) (law P Itil ∗ γ) ≤
      (∫⁻ ω, ENNReal.ofReal (‖Iemp ω - Itil ω‖ ^ p) ∂P) ^ (1 / p) +
      ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) +
      (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, e, B, S, Sb, G, -, -, -, -, -, -, -, hGm, hGind, hGc,
    hGcov, hbound⟩ := hilbert_polar_coupling P ℱ t ht ⟨ℱ 0, le_rfl⟩ W hW Φ hΦ M hM sb hsb
  obtain ⟨hγp, hγc, hγcov⟩ := hγ
  have hIm : Measurable Iemp := hI.mono (ℱ.le 0) le_rfl
  have hMm : Measurable (M t) := (hM.adapted t).mono (ℱ.le t) le_rfl
  have hqmp := hπ.quasiMeasurePreserving
  -- the Gaussian law
  have hγeq : law P' (G t) = γ := by
    haveI := hGc.1
    haveI := hγp
    refine Measure.ext_of_charFun (funext fun u => ?_)
    rw [HilbertCLTAux.charFun_centered_gaussian hGc, HilbertCLTAux.charFun_centered_gaussian hγc,
      hGcov, hγcov]
  -- pull-backs
  have hZm : AEMeasurable Z P := by
    refine ((hIm.aemeasurable.add hMm.aemeasurable).add hR).congr ?_
    filter_upwards [hZ] with ω h using h.symm
  have hlawZ : law P' (fun ω' => Z (π ω')) = law P Z := by
    show P'.map (Z ∘ π) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hπ.map_eq]) hπ.aemeasurable, hπ.map_eq]
  have hlawI : law P' (fun ω' => Iemp (π ω')) = law P Iemp := by
    show P'.map (Iemp ∘ π) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hIm.aemeasurable)
      hπ.aemeasurable, hπ.map_eq]
  have hIπ : Measurable fun ω' => Iemp (π ω') := hIm.comp hπ.measurable
  have hMπ : Measurable fun ω' => M t (π ω') := hMm.comp hπ.measurable
  have hRπ : AEMeasurable (fun ω' => R (π ω')) P' := hR.comp_quasiMeasurePreserving hqmp
  have hItπ : AEMeasurable (fun ω' => Itil (π ω')) P' := hIt.comp_quasiMeasurePreserving hqmp
  -- 𝒢-measurability of the initial term on the enlargement
  set 𝒢 : SubSigma Ω' mΩ' := ⟨(ℱ 0).comap π, hπ.measurable.comap_le.trans' (by
    exact (MeasurableSpace.comap_mono (ℱ.le 0)))⟩ with h𝒢
  have hIG : Measurable[𝒢.1] fun ω' => Iemp (π ω') :=
    hI.comp (comap_measurable π)
  have hGind' : Indep 𝒢.1 (MeasurableSpace.comap (G t) inferInstance) P' := hGind
  -- triangle inequalities
  haveI : IsProbabilityMeasure (law P' fun ω' => Z (π ω')) := by rw [hlawZ]; infer_instance
  haveI : IsProbabilityMeasure (law P' fun ω' => Iemp (π ω') + M t (π ω')) :=
    inferInstance
  haveI : IsProbabilityMeasure (law P' fun ω' => Iemp (π ω') + G t ω') :=
    inferInstance
  haveI : IsProbabilityMeasure γ := hγp
  haveI : IsProbabilityMeasure (law P Itil) := inferInstance
  haveI : IsProbabilityMeasure (law P Iemp) := inferInstance
  haveI : IsProbabilityMeasure (law P Itil ∗ γ) := inferInstance
  have t1 := wassersteinE_triangle p hp1 (law P' fun ω' => Z (π ω'))
    (law P' fun ω' => Iemp (π ω') + M t (π ω')) (law P Itil ∗ γ)
  have t2 := wassersteinE_triangle p hp1 (law P' fun ω' => Iemp (π ω') + M t (π ω'))
    (law P' fun ω' => Iemp (π ω') + G t ω') (law P Itil ∗ γ)
  -- term 1: the remainder
  have c1 := wassersteinE_le_of_coupling P' p hp1 (fun ω' => Z (π ω'))
    (fun ω' => Iemp (π ω') + M t (π ω')) (hZm.comp_quasiMeasurePreserving hqmp)
    (hIπ.add hMπ).aemeasurable
  have hc1 : ∫⁻ ω', ENNReal.ofReal (‖Z (π ω') - (Iemp (π ω') + M t (π ω'))‖ ^ p) ∂P' =
      ∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P := by
    have hfm : AEMeasurable (fun ω => ENNReal.ofReal (‖R ω‖ ^ p)) P :=
      (hR.norm.pow_const p).ennreal_ofReal
    have := lintegral_map' (μ := P') (f := fun ω => ENNReal.ofReal (‖R ω‖ ^ p)) (g := π)
      (by rw [hπ.map_eq]; exact hfm) hπ.aemeasurable
    rw [hπ.map_eq] at this
    rw [this]
    refine lintegral_congr_ae ?_
    filter_upwards [hqmp.ae hZ] with ω' h
    rw [h]
    simp
  -- term 2: the DDS-type coupling
  have c2 := wassersteinE_le_of_coupling P' p hp1 (fun ω' => Iemp (π ω') + M t (π ω'))
    (fun ω' => Iemp (π ω') + G t ω') (hIπ.add hMπ).aemeasurable (hIπ.aemeasurable.add hGm)
  have hc2 : (∫⁻ ω', ENNReal.ofReal (‖(Iemp (π ω') + M t (π ω')) - (Iemp (π ω') + G t ω')‖ ^ p) ∂P') ^ (1 / p)
      ≤ ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) := by
    have e : ∀ ω', ENNReal.ofReal (‖(Iemp (π ω') + M t (π ω')) - (Iemp (π ω') + G t ω')‖ ^ p) =
        (‖M t (π ω') - G t ω'‖ₑ) ^ p := fun ω' => by
      rw [add_sub_add_left_eq_sub, ofReal_norm_rpow hp0.le, ofReal_norm_eq_enorm]
    simp only [e]
    have := lintegral_rpow_mono P' (fun ω' => ‖M t (π ω') - G t ω'‖ₑ) hp0 hp2
    refine this.trans ?_
    have h2 : (∫⁻ ω', ‖M t (π ω') - G t ω'‖ₑ ^ (2 : ℝ) ∂P') ^ (1 / (2:ℝ)) ≤
        (ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) ^ (1 / (2:ℝ)) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      simpa [ENNReal.rpow_two] using hbound
    refine h2.trans (le_of_eq ?_)
    by_cases hD0 : 0 ≤ covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb
    · rw [ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num), Real.sqrt_eq_rpow, one_div]
    · push Not at hD0
      rw [ENNReal.ofReal_of_nonpos hD0.le, Real.sqrt_eq_zero_of_nonpos hD0.le]
      simp
  -- term 3: the initial term
  have hlawsum : law P' (fun ω' => Iemp (π ω') + G t ω') = law P' (fun ω' => Iemp (π ω')) ∗ γ := by
    rw [law_add_indep P' 𝒢 _ _ hIG hGm hGind', hγeq]
    rfl
  have c3 : wassersteinE p (law P' fun ω' => Iemp (π ω') + G t ω') (law P Itil ∗ γ) ≤
      (∫⁻ ω, ENNReal.ofReal (‖Iemp ω - Itil ω‖ ^ p) ∂P) ^ (1 / p) := by
    rw [hlawsum, hlawI]
    refine (a8p_wass_conv_le p hp1 (law P Iemp) (law P Itil) γ).trans ?_
    exact wassersteinE_le_of_coupling P p hp1 Iemp Itil hIm.aemeasurable hIt
  rw [← hlawZ]
  calc _ ≤ _ := t1
    _ ≤ wassersteinE p (law P' fun ω' => Z (π ω')) (law P' fun ω' => Iemp (π ω') + M t (π ω')) +
        (wassersteinE p (law P' fun ω' => Iemp (π ω') + M t (π ω'))
          (law P' fun ω' => Iemp (π ω') + G t ω') +
         wassersteinE p (law P' fun ω' => Iemp (π ω') + G t ω') (law P Itil ∗ γ)) :=
      add_le_add le_rfl t2
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) +
        (ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) +
         (∫⁻ ω, ENNReal.ofReal (‖Iemp ω - Itil ω‖ ^ p) ∂P) ^ (1 / p)) := by
      refine add_le_add ?_ (add_le_add (c2.trans hc2) c3)
      rw [← hc1]; exact c1
    _ = _ := by ring

end Wass

end HRS.Main.A8P
