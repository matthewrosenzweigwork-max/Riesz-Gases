import HRS.MS.S82RB2

/-!
# S8.2 R01B (S82R), part 3: conditional variance, one-site kernel = `resampleLaw`, resampling adapter
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}

/-- The variance is at most the mean square deviation from any constant (in `ℝ≥0∞`). -/
lemma s82r_evariance_le_sq {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (g : E → ℝ) (hg : Measurable g) (c : ℝ) :
    evariance g ν ≤ ∫⁻ y, ENNReal.ofReal ((g y - c) ^ 2) ∂ν := by
  by_cases hfin : ∫⁻ y, ENNReal.ofReal ((g y - c) ^ 2) ∂ν = ⊤
  · rw [hfin]; exact le_top
  have hgc : Measurable (fun y => g y - c) := hg.sub_const c
  have hint : Integrable (fun y => (g y - c) ^ 2) ν := by
    have hm : AEStronglyMeasurable (fun y => (g y - c) ^ 2) ν :=
      (hgc.pow_const 2).aestronglyMeasurable
    exact (lintegral_ofReal_ne_top_iff_integrable hm (ae_of_all _ fun y => sq_nonneg _)).1 hfin
  have hL : MemLp (fun y => g y - c) 2 ν :=
    (memLp_two_iff_integrable_sq hgc.aestronglyMeasurable).2 hint
  have hLg : MemLp g 2 ν := by
    have := hL.add (memLp_const c)
    have e : ((fun y => g y - c) + fun _ => c) = g := by funext y; simp
    rwa [e] at this
  rw [← ofReal_variance hLg, variance_sub_const hg.aestronglyMeasurable c |>.symm]
  have h1 := variance_le_expectation_sq (μ := ν) hgc.aestronglyMeasurable
  calc ENNReal.ofReal (variance (fun y => g y - c) ν)
      ≤ ENNReal.ofReal (ν[(fun y => g y - c) ^ 2]) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ y, ENNReal.ofReal ((g y - c) ^ 2) ∂ν := by
        have := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => sq_nonneg _)
        simpa [Pi.pow_apply] using this


open HRS.External in
/-- The one-site kernel of the pinned weak ensemble is `resampleLaw`. -/
lemma s82r_siteKernel_eq (hd : 2 ≤ d) (hbeta : 0 < beta)
    (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ}
    (pins : Fin p → Euc d) (i : Fin n) (X : EucConfig d n) :
    haveI := s82r_isProb hρ
    siteKernel (HRS.Whole.withDensityReal rho)
      (pinnedDensity (s82r_pot hd hbeta hD hG hρ hρG hN) (beta / N) n pins) i X =
      resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X := by
  haveI := s82r_isProb hρ
  set μ := HRS.Whole.withDensityReal rho with hμ
  set V := s82r_pot hd hbeta hD hG hρ hρG hN with hV
  have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta.le (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam pins
  have hVφ : V.φ = s82r_phi q h μ beta N := rfl
  have hVq : ∀ x y, V.q x y = q (x - y) := fun x y => rfl
  show siteKernel μ (fieldDensity V (pinField V (beta / N) pins) (beta / N) n) i X = _
  rw [siteKernel_fieldDensity (V := V) hψ hlam]
  have hs : ∀ z, siteU V (pinField V (beta / N) pins) (beta / N) i X z = Real.exp (
      beta * HRS.Whole.convMeasure q μ z + h N z - (beta / N) *
        ((∑ j ∈ Finset.univ.erase i, q (z - X j)) + ∑ j, q (z - pins j))) := by
    intro z
    unfold siteU pinField
    simp only [hVφ, hVq, s82r_phi]
    congr 1
    ring
  have hIpos : 0 < ∫ z, siteU V (pinField V (beta / N) pins) (beta / N) i X z ∂μ :=
    integral_siteU_pos hψ hlam i X
  unfold resampleLaw exponentialTilt
  have hI : ∫ z, Real.exp (beta * HRS.Whole.convMeasure q μ z + h N z - (beta / N) *
        ((∑ j ∈ Finset.univ.erase i, q (z - X j)) + ∑ j, q (z - pins j))) ∂μ =
      ∫ z, siteU V (pinField V (beta / N) pins) (beta / N) i X z ∂μ :=
    integral_congr_ae (ae_of_all _ fun z => (hs z).symm)
  rw [hI]
  have hsm : Measurable (fun z => ENNReal.ofReal (siteU V (pinField V (beta / N) pins) (beta / N) i X z)) :=
    (measurable_siteU hψ.measurable V _ i X).ennreal_ofReal
  have e : (fun z => ENNReal.ofReal (siteU V (pinField V (beta / N) pins) (beta / N) i X z /
      ∫ z', siteU V (pinField V (beta / N) pins) (beta / N) i X z' ∂μ)) =
      (ENNReal.ofReal (∫ z', siteU V (pinField V (beta / N) pins) (beta / N) i X z' ∂μ))⁻¹ •
        fun z => ENNReal.ofReal (siteU V (pinField V (beta / N) pins) (beta / N) i X z) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hIpos.le),
      ENNReal.ofReal_inv_of_pos hIpos]
  rw [e, withDensity_smul _ hsm]
  congr 2
  funext z
  rw [hs z]


lemma s82r_wu_smallness :
    beta * (1 / (1000 * beta)) ≤ min 1 (1 / (16 * Real.exp (1 + 1 / 1000 + 1 + 1))) ∨ beta ≤ 0 := by
  by_cases hb : 0 < beta
  · left
    have e : beta * (1 / (1000 * beta)) = 1 / 1000 := by field_simp
    rw [e]
    refine le_min (by norm_num) ?_
    have h1 : Real.exp (1 + 1 / 1000 + 1 + 1) ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h4 : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 :=
      pow_lt_pow_left₀ h3 (Real.exp_pos _).le (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [Real.exp_pos (1 + 1 / 1000 + 1 + 1)]
  · right; exact not_lt.1 hb

open HRS.External in
/-- Resampling inequality for the displayed reference law (constant `2`). -/
theorem s82r_resampling (hd : 2 ≤ d) (hbeta : 0 < beta)
    (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ}
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) (F : EucConfig d n → ℝ)
    (hF : MemLp F 2 (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins)) :
    evariance F (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) ≤
      ENNReal.ofReal 2 * ∑ i,
        ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
            ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins := by
  haveI := s82r_isProb hρ
  set μ := HRS.Whole.withDensityReal rho with hμ
  set V := s82r_pot hd hbeta hD hG hρ hρG hN with hV
  have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta.le (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam pins
  have hRe := s82r_referenceLaw_eq hd hbeta hD hG hρ hρG hN (n := n) pins
  rw [hRe] at hF ⊢
  set Pr := pinnedLaw V (beta / N) n pins with hR
  haveI : IsProbabilityMeasure Pr := isProb_pinnedLaw V hlam n pins
  have hKeq : ∀ (i : Fin n) (X : EucConfig d n),
      siteKernel μ (pinnedDensity V (beta / N) n pins) i X =
        resampleLaw q h μ beta N pins i X :=
    fun i X => s82r_siteKernel_eq hd hbeta hD hG hρ hρG hN pins i X
  haveI hmk : ∀ i : Fin n, IsMarkovKernel (siteKernel μ (pinnedDensity V (beta / N) n pins) i) :=
    fun i => (fieldSpec (V := V) hψ hlam n).isMarkov i
  have hK := s82r_weakKernel hd hbeta hD hG hρ hρG
  have hφ := s82r_isField hd hbeta hD hG hρ hρG hN
  have hN0 : 0 < N := by omega
  have hcard : n + Fintype.card (Fin p) ≤ N := by simpa using hnp
  have hs : beta * (1 / (1000 * beta)) ≤ min 1 (1 / (16 * Real.exp (1 + 1 / 1000 + 1 + 1))) := by
    rcases s82r_wu_smallness (beta := beta) with h | h
    · exact h
    · exact absurd h (not_le.2 hbeta)
  -- measurable representative
  set Fh := hF.aestronglyMeasurable.mk F with hFh
  have hFhm : Measurable Fh := hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : F =ᵐ[Pr] Fh := hF.aestronglyMeasurable.ae_eq_mk
  have hwu := HRS.MS.Wl.wl_resampling hK (by positivity) hφ hbeta.le hN0 hcard pins hs Fh hFhm
  have hwu' : evariance Fh Pr ≤ 2 * ∑ i, ∫⁻ x, evariance (fun w => Fh (Function.update x i w))
      (siteKernel μ (pinnedDensity V (beta / N) n pins) i x) ∂Pr := hwu
  obtain ⟨T, hTsub, hTm, hT0⟩ := exists_measurable_superset_of_null
    (show Pr {X | ¬ F X = Fh X} = 0 from ae_iff.1 hae)
  have hinv : ∀ i : Fin n, ∀ᵐ X ∂Pr, ∀ᵐ y ∂(resampleLaw q h μ beta N pins i X),
      Function.update X i y ∉ T := by
    intro i
    have h1 : ∫⁻ x, ∫⁻ z, T.indicator (1 : (Fin n → Euc d) → ℝ≥0∞) (Function.update x i z)
        ∂(siteKernel μ (pinnedDensity V (beta / N) n pins) i x) ∂Pr =
        ∫⁻ x, T.indicator (1 : (Fin n → Euc d) → ℝ≥0∞) x ∂Pr :=
      (fieldSpec (V := V) hψ hlam n).invariant i _ (measurable_one.indicator hTm)
    rw [lintegral_indicator_one hTm, hT0] at h1
    have hm : Measurable (fun p : (Fin n → Euc d) × Euc d =>
        T.indicator (1 : (Fin n → Euc d) → ℝ≥0∞) (Function.update p.1 i p.2)) :=
      (measurable_one.indicator hTm).comp measurable_update'
    have hm2 := hm.lintegral_kernel_prod_right' (κ := siteKernel μ (pinnedDensity V (beta / N) n pins) i)
    have h2 := (lintegral_eq_zero_iff hm2).1 h1
    filter_upwards [h2] with X hX
    rw [← hKeq i X]
    have hm3 : Measurable (fun z => T.indicator (1 : (Fin n → Euc d) → ℝ≥0∞) (Function.update X i z)) :=
      (measurable_one.indicator hTm).comp (measurable_update X)
    have := (lintegral_eq_zero_iff hm3).1 hX
    filter_upwards [this] with y hy
    intro hyT
    simp [Set.indicator_of_mem hyT] at hy
  have hcongr : ∀ i : Fin n, ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
        ∂resampleLaw q h μ beta N pins i X) ∂Pr =
      ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((Fh (Function.update X i y) - Fh X) ^ 2)
        ∂resampleLaw q h μ beta N pins i X) ∂Pr := by
    intro i
    refine lintegral_congr_ae ?_
    filter_upwards [hinv i, hae] with X hX hFX
    refine lintegral_congr_ae ?_
    filter_upwards [hX] with y hy
    have : F (Function.update X i y) = Fh (Function.update X i y) := by
      by_contra hne; exact hy (hTsub hne)
    rw [this, hFX]
  have hstep : ∀ i : Fin n, ∀ X : EucConfig d n,
      evariance (fun w => Fh (Function.update X i w))
        (siteKernel μ (pinnedDensity V (beta / N) n pins) i X) ≤
      ∫⁻ y, ENNReal.ofReal ((Fh (Function.update X i y) - Fh X) ^ 2)
        ∂resampleLaw q h μ beta N pins i X := by
    intro i X
    haveI := (hmk i)
    rw [← hKeq i X]
    exact s82r_evariance_le_sq _ _ (hFhm.comp (measurable_update X)) (Fh X)
  calc evariance F Pr = evariance Fh Pr := evariance_congr hae
    _ ≤ 2 * ∑ i, ∫⁻ x, evariance (fun w => Fh (Function.update x i w))
        (siteKernel μ (pinnedDensity V (beta / N) n pins) i x) ∂Pr := hwu'
    _ ≤ ENNReal.ofReal 2 * ∑ i, ∫⁻ X, (∫⁻ y,
          ENNReal.ofReal ((Fh (Function.update X i y) - Fh X) ^ 2)
            ∂resampleLaw q h μ beta N pins i X) ∂Pr := by
        rw [ENNReal.ofReal_ofNat]
        gcongr with i _ X
        exact hstep i X
    _ = ENNReal.ofReal 2 * ∑ i, ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
          ∂resampleLaw q h μ beta N pins i X) ∂Pr := by
        simp_rw [hcongr]

end HRS.MS.S82R

end
