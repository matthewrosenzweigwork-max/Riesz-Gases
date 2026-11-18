import HRS.Main.A8PAux2
import HRS.Main.A1014Aux3

/-!
# Packet A1014, part 4: the abstract `W_p` chain with a finite-mode martingale in a Hilbert space `E`

`a1014_wass_abstract`: `Z, X, Xt : Ω → E` (`E` the full field space), `M` an `ℝ^q`-valued Hilbert Itô integral,
`J : ℝ^q → E` a contraction, `c : E → ℝ^q` measurable with `νG.map c = γ` (the centred Gaussian of covariance
`∫ Σ̄`).  For `p ∈ [1,2]`,
`W_p(Law Z, Law Xt ∗ νG) ≤ ‖Z - X - J M_t‖_p + (D)^{1/2} + ‖X - Xt‖_p + ‖y - J c y‖_{L^p(νG)}`
(four-term chain: remainder, polar coupling in `ℝ^q`, initial term, Gaussian tail).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

section WassAbs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem a1014_wass_abstract {q : ℕ} (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → (ℝ^q)) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → (ℝ^q)) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → ((ℝ^q) →L[ℝ] (ℝ^q) →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb)
    (γ : Measure (ℝ^q)) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (J : (ℝ^q) →L[ℝ] H) (hJ : ‖J‖ ≤ 1) (c : H → (ℝ^q)) (hc : Measurable c)
    (νG : Measure H) [IsProbabilityMeasure νG] (hνγ : νG.map c = γ)
    (X Xt Z : Ω → H) (hX : Measurable[ℱ 0] X) (hXt : AEMeasurable Xt P) (hZ : AEMeasurable Z P)
    (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    wassersteinE p (law P Z) (law P Xt ∗ νG) ≤
      (∫⁻ ω, ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p) ∂P) ^ (1 / p) +
      ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) +
      (∫⁻ ω, ENNReal.ofReal (‖X ω - Xt ω‖ ^ p) ∂P) ^ (1 / p) +
      (∫⁻ y, ENNReal.ofReal (‖y - J (c y)‖ ^ p) ∂νG) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, e, B, S, Sb, G, -, -, -, -, -, -, -, hGm, hGind, hGc,
    hGcov, hbound⟩ := hilbert_polar_coupling P ℱ t ht ⟨ℱ 0, le_rfl⟩ W hW Φ hΦ M hM sb hsb
  obtain ⟨hγp, hγc, hγcov⟩ := hγ
  have := hP'
  have := hγp
  have hJc : Continuous J := J.continuous
  have hJm : Measurable J := hJc.measurable
  have hXm : Measurable X := hX.mono (ℱ.le 0) le_rfl
  have hMm : Measurable (M t) := (hM.adapted t).mono (ℱ.le t) le_rfl
  have hqmp := hπ.quasiMeasurePreserving
  -- the Gaussian law
  have hγeq : law P' (G t) = γ := by
    have := hGc.1
    refine Measure.ext_of_charFun (funext fun u => ?_)
    rw [HilbertCLTAux.charFun_centered_gaussian hGc, HilbertCLTAux.charFun_centered_gaussian hγc,
      hGcov, hγcov]
  set γJ : Measure H := γ.map J with hγJ
  have : IsProbabilityMeasure γJ := inferInstance
  -- pull-backs
  have hZπ : AEMeasurable (fun ω' => Z (π ω')) P' := hZ.comp_quasiMeasurePreserving hqmp
  have hXπ : Measurable fun ω' => X (π ω') := hXm.comp hπ.measurable
  have hMπ : Measurable fun ω' => M t (π ω') := hMm.comp hπ.measurable
  have hJMπ : Measurable fun ω' => J (M t (π ω')) := hJm.comp hMπ
  have hJGπ : AEMeasurable (fun ω' => J (G t ω')) P' := hJm.comp_aemeasurable hGm
  have hlawZ : law P' (fun ω' => Z (π ω')) = law P Z := by
    show P'.map (Z ∘ π) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hπ.map_eq]) hπ.aemeasurable, hπ.map_eq]
  have hlawX : law P' (fun ω' => X (π ω')) = law P X := by
    show P'.map (X ∘ π) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by rw [hπ.map_eq]; exact hXm.aemeasurable)
      hπ.aemeasurable, hπ.map_eq]
  -- the initial σ-algebra on the enlargement
  set 𝒢 : SubSigma Ω' mΩ' := ⟨(ℱ 0).comap π, hπ.measurable.comap_le.trans' (by
    exact (MeasurableSpace.comap_mono (ℱ.le 0)))⟩ with h𝒢
  have hXG : Measurable[𝒢.1] fun ω' => X (π ω') := hX.comp (comap_measurable π)
  have hGind' : Indep 𝒢.1 (MeasurableSpace.comap (G t) inferInstance) P' := hGind
  have hle : MeasurableSpace.comap (fun ω' => J (G t ω')) (inferInstance : MeasurableSpace H) ≤
      MeasurableSpace.comap (G t) (inferInstance : MeasurableSpace (ℝ^q)) := by
    rw [show (fun ω' => J (G t ω')) = J ∘ G t from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hJm.comap_le
  have hind2 : Indep 𝒢.1 (MeasurableSpace.comap (fun ω' => J (G t ω')) inferInstance) P' :=
    indep_of_indep_of_le_right hGind' hle
  have hlawJG : law P' (fun ω' => J (G t ω')) = γJ := by
    show P'.map (J ∘ G t) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hJm.aemeasurable hGm, hγJ]
    exact congrArg (fun μ => μ.map J) hγeq
  have hlawsum : law P' (fun ω' => X (π ω') + J (G t ω')) = law P X ∗ γJ := by
    rw [law_add_indep P' 𝒢 _ _ hXG hJGπ hind2, hlawX, hlawJG]
    rfl
  -- the measures of the chain
  have : IsProbabilityMeasure (law P Z) := inferInstance
  have : IsProbabilityMeasure (law P X) := inferInstance
  have : IsProbabilityMeasure (law P Xt) := inferInstance
  have hB : AEMeasurable (fun ω' => X (π ω') + J (M t (π ω'))) P' :=
    (hXπ.add hJMπ).aemeasurable
  have hC : AEMeasurable (fun ω' => X (π ω') + J (G t ω')) P' := hXπ.aemeasurable.add hJGπ
  have : IsProbabilityMeasure (law P' (fun ω' => Z (π ω'))) := inferInstance
  have : IsProbabilityMeasure (law P' (fun ω' => X (π ω') + J (M t (π ω')))) := inferInstance
  have : IsProbabilityMeasure (law P' (fun ω' => X (π ω') + J (G t ω'))) := inferInstance
  have : IsProbabilityMeasure (law P Xt ∗ γJ) := inferInstance
  have : IsProbabilityMeasure (law P X ∗ γJ) := inferInstance
  have : IsProbabilityMeasure (law P Xt ∗ νG) := inferInstance
  have t1 := wassersteinE_triangle p hp1 (law P' fun ω' => Z (π ω'))
    (law P' fun ω' => X (π ω') + J (M t (π ω'))) (law P Xt ∗ νG)
  have t2 := wassersteinE_triangle p hp1 (law P' fun ω' => X (π ω') + J (M t (π ω')))
    (law P' fun ω' => X (π ω') + J (G t ω')) (law P Xt ∗ νG)
  have t3 := wassersteinE_triangle p hp1 (law P' fun ω' => X (π ω') + J (G t ω'))
    (law P Xt ∗ γJ) (law P Xt ∗ νG)
  -- term 1: the remainder
  have c1 := wassersteinE_le_of_coupling P' p hp1 (fun ω' => Z (π ω'))
    (fun ω' => X (π ω') + J (M t (π ω'))) hZπ hB
  have hc1 : ∫⁻ ω', ENNReal.ofReal (‖Z (π ω') - (X (π ω') + J (M t (π ω')))‖ ^ p) ∂P' =
      ∫⁻ ω, ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p) ∂P := by
    have hfm : AEMeasurable (fun ω => ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p)) P :=
      (((hZ.sub hXm.aemeasurable).sub (hJm.comp hMm).aemeasurable).norm.pow_const p).ennreal_ofReal
    have := lintegral_map' (μ := P') (f := fun ω => ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p))
      (g := π) (by rw [hπ.map_eq]; exact hfm) hπ.aemeasurable
    rw [hπ.map_eq] at this
    rw [this]
    refine lintegral_congr_ae (Eventually.of_forall fun ω' => ?_)
    simp only [sub_add_eq_sub_sub]
  -- term 2: the polar coupling
  have c2 := wassersteinE_le_of_coupling P' p hp1 (fun ω' => X (π ω') + J (M t (π ω')))
    (fun ω' => X (π ω') + J (G t ω')) hB hC
  have hc2 : (∫⁻ ω', ENNReal.ofReal (‖(X (π ω') + J (M t (π ω'))) - (X (π ω') + J (G t ω'))‖ ^ p)
      ∂P') ^ (1 / p) ≤
      ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) := by
    have e : ∀ ω', ENNReal.ofReal (‖(X (π ω') + J (M t (π ω'))) - (X (π ω') + J (G t ω'))‖ ^ p) ≤
        (‖M t (π ω') - G t ω'‖ₑ) ^ p := fun ω' => by
      rw [add_sub_add_left_eq_sub, ← map_sub, ← ofReal_norm_eq_enorm,
        ← ofReal_norm_rpow hp0.le]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) ?_ hp0.le)
      exact (J.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    have hmono := lintegral_mono (μ := P') e
    have h1 := lintegral_rpow_mono P' (fun ω' => ‖M t (π ω') - G t ω'‖ₑ) hp0 hp2
    have h2 : (∫⁻ ω', ‖M t (π ω') - G t ω'‖ₑ ^ (2 : ℝ) ∂P') ^ (1 / (2:ℝ)) ≤
        (ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) ^ (1 / (2:ℝ)) := by
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      simpa [ENNReal.rpow_two] using hbound
    refine (ENNReal.rpow_le_rpow hmono (by positivity)).trans (h1.trans (h2.trans (le_of_eq ?_)))
    by_cases hD0 : 0 ≤ covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb
    · rw [ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num), Real.sqrt_eq_rpow, one_div]
    · push Not at hD0
      rw [ENNReal.ofReal_of_nonpos hD0.le, Real.sqrt_eq_zero_of_nonpos hD0.le]
      simp
  -- term 3: the initial term
  have c3' : wassersteinE p (law P X ∗ γJ) (law P Xt ∗ γJ) ≤
      (∫⁻ ω, ENNReal.ofReal (‖X ω - Xt ω‖ ^ p) ∂P) ^ (1 / p) := by
    refine (HRS.Main.A8P.a8p_wass_conv_le p hp1 (law P X) (law P Xt) γJ).trans ?_
    exact wassersteinE_le_of_coupling P p hp1 X Xt hXm.aemeasurable hXt
  -- term 4: the Gaussian tail
  have c4 : wassersteinE p (law P Xt ∗ γJ) (law P Xt ∗ νG) ≤
      (∫⁻ y, ENNReal.ofReal (‖y - J (c y)‖ ^ p) ∂νG) ^ (1 / p) := by
    rw [Measure.conv_comm (law P Xt) γJ, Measure.conv_comm (law P Xt) νG]
    refine (HRS.Main.A8P.a8p_wass_conv_le p hp1 γJ νG (law P Xt)).trans ?_
    have hlaw : γJ = law νG (fun y => J (c y)) := by
      show γ.map J = νG.map (J ∘ c)
      rw [← Measure.map_map hJm hc, hνγ]
    have := wassersteinE_le_of_coupling νG p hp1 (fun y => J (c y)) (fun y => y)
      (hJm.comp hc).aemeasurable aemeasurable_id
    rw [← hlaw] at this
    simp only [law, Measure.map_id'] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun y => ?_
    rw [norm_sub_rev]
  rw [← hlawZ]
  have hfin : wassersteinE p (law P' fun ω' => Z (π ω')) (law P Xt ∗ νG) ≤
      wassersteinE p (law P' fun ω' => Z (π ω')) (law P' fun ω' => X (π ω') + J (M t (π ω'))) +
      (wassersteinE p (law P' fun ω' => X (π ω') + J (M t (π ω'))) (law P' fun ω' => X (π ω') + J (G t ω')) +
       (wassersteinE p (law P' fun ω' => X (π ω') + J (G t ω')) (law P Xt ∗ γJ) +
        wassersteinE p (law P Xt ∗ γJ) (law P Xt ∗ νG))) := by
    refine t1.trans (add_le_add le_rfl ?_)
    refine t2.trans (add_le_add le_rfl ?_)
    exact t3
  have hw3 : wassersteinE p (law P' fun ω' => X (π ω') + J (G t ω')) (law P Xt ∗ γJ) ≤
      (∫⁻ ω, ENNReal.ofReal (‖X ω - Xt ω‖ ^ p) ∂P) ^ (1 / p) := by
    rw [hlawsum]; exact c3'
  refine hfin.trans ?_
  have h1 : wassersteinE p (law P' fun ω' => Z (π ω'))
      (law P' fun ω' => X (π ω') + J (M t (π ω'))) ≤
      (∫⁻ ω, ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p) ∂P) ^ (1 / p) := by
    refine c1.trans (le_of_eq ?_)
    rw [hc1]
  have h2 : wassersteinE p (law P' fun ω' => X (π ω') + J (M t (π ω')))
      (law P' fun ω' => X (π ω') + J (G t ω')) ≤
      ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) :=
    c2.trans hc2
  calc _ ≤ (∫⁻ ω, ENNReal.ofReal (‖Z ω - X ω - J (M t ω)‖ ^ p) ∂P) ^ (1 / p) +
        (ENNReal.ofReal (Real.sqrt (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb)) +
         ((∫⁻ ω, ENNReal.ofReal (‖X ω - Xt ω‖ ^ p) ∂P) ^ (1 / p) +
          (∫⁻ y, ENNReal.ofReal (‖y - J (c y)‖ ^ p) ∂νG) ^ (1 / p))) :=
        add_le_add h1 (add_le_add h2 (add_le_add hw3 c4))
    _ = _ := by ring

end WassAbs

end HRS.Main.A1014
