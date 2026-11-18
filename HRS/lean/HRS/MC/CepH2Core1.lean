import HRS.MC.CepH2Aux31
import HRS.MC.CepH2Init4

/-!
# CEPH2, C6 (a): the mollified dissipation inequality with the extended-valued dissipation
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem cepH2_clampSet {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) {θ : ℝ} (hθ : 0 < θ) {μ : ℝ → Measure (Ch N)}
    [∀ t, IsProbabilityMeasure (μ t)] (hcell : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0) {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : Ch N → ℝ, Continuous g → (∀ z, g (z + cep_diag N) = g z) → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : H2WeakFP θ U μ) {v : ℝ} (hv : 0 < v) :
    ∃ M : ℝ, H2Set θ v U K (fun s => μ (h2_clamp T s)) T M := by
  obtain ⟨M, hMtop, hM⟩ := hmom
  set μ' : ℝ → Measure (Ch N) := fun s => μ (h2_clamp T s) with hμ'
  have hmeas : Measurable fun z : Ch N => ‖h2_perp z‖ ^ 2 := (h2_continuous_perp.norm.pow 2).measurable
  have hint : ∀ s, Integrable (fun y => ‖h2_perp y‖ ^ 2) (μ' s) := fun s => by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)]
    exact lt_of_le_of_lt (hM _ (h2_clamp_mem hT s)) hMtop
  refine ⟨M.toReal, ?_⟩
  exact
    { hθ := hθ
      hv := hv
      hU := hU
      hUper := hUper
      hK := hK
      hT := hT
      hprob := fun s => inferInstanceAs (IsProbabilityMeasure (μ (h2_clamp T s)))
      hcell := fun s => hcell _ (h2_clamp_mem hT s).1
      hmom := hint
      hM := fun s => by
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => by positivity) hmeas.aestronglyMeasurable]
        exact ENNReal.toReal_mono hMtop.ne (hM _ (h2_clamp_mem hT s))
      hnar := fun g hg hper hb => (hnar g hg hper hb).comp_continuous (h2_continuous_clamp T)
        (h2_clamp_mem hT)
      hfp := fun g hg s hs => by
        have h1 : ∀ r ∈ Icc (0 : ℝ) T, μ' r = μ r := fun r hr => by simp only [hμ', h2_clamp_of_mem hr]
        have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
        rw [h1 s hs, h1 0 h0]
        have := hfp g hg s hs.1
        rw [this]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        simp only [h1 r ⟨hr.1, hr.2.trans hs.2⟩] }

theorem cepH2_mollified_full {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) {θ : ℝ} (hθ : 0 < θ) {μ : ℝ → Measure (Ch N)}
    [∀ t, IsProbabilityMeasure (μ t)] (hcell : ∀ t, 0 ≤ t → μ t (cep_cell N)ᶜ = 0) {T : ℝ} (hT : 0 ≤ T)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂(μ t) ≤ M)
    (hnar : ∀ g : Ch N → ℝ, Continuous g → (∀ z, g (z + cep_diag N) = g z) → (∃ C : ℝ, ∀ z, |g z| ≤ C) →
      ContinuousOn (fun t => ∫ z, g z ∂(μ t)) (Icc (0 : ℝ) T))
    (hfp : H2WeakFP θ U μ) {v : ℝ} (hv : 0 < v) :
    AEMeasurable (h2_Dinf θ v U μ) (volume.restrict (Icc (0 : ℝ) T)) ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t ∈ Icc (0 : ℝ) T,
      ∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ v U μ r ≠ ⊤ ∧
      h2_free θ U (h2_mu v (μ t)) + θ * (1 - δ) * (∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ v U μ r).toReal ≤
        h2_free θ U (h2_mu v (μ 0)) + t * ((K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)) := by
  obtain ⟨M, S⟩ := cepH2_clampSet hU hUper hK hθ hcell hT hmom hnar hfp hv
  set μ' : ℝ → Measure (Ch N) := fun s => μ (h2_clamp T s) with hμ'
  have h1 : ∀ r ∈ Icc (0 : ℝ) T, μ' r = μ r := fun r hr => by simp only [hμ', h2_clamp_of_mem hr]
  have hD : ∀ r ∈ Icc (0 : ℝ) T, h2_Dinf θ v U μ' r = h2_Dinf θ v U μ r := fun r hr => by
    simp only [h2_Dinf, h1 r hr]
  refine ⟨?_, fun δ hδ hδ1 t ht => ?_⟩
  · refine S.meas_Dinf.aemeasurable.congr ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hD r hr)
  · have ht0 := ht.1
    have hsub : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
    have hcongr : ∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ v U μ' r = ∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ v U μ r :=
      setLIntegral_congr_fun measurableSet_Icc (fun r hr => hD r (hsub r hr))
    obtain ⟨hfin, hineq⟩ := S.result2' hδ hδ1 ht
    refine ⟨hcongr ▸ hfin, ?_⟩
    have hI : ∫ r in Icc (0 : ℝ) t, h2_diss θ U (h2_mu v (μ' r)) =
        (∫⁻ r in Icc (0 : ℝ) t, h2_Dinf θ v U μ' r).toReal := by
      have e : (fun r => h2_diss θ U (h2_mu v (μ' r))) = fun r => (h2_Dinf θ v U μ' r).toReal :=
        funext fun r => S.diss_eq r
      rw [e, integral_toReal S.meas_Dinf.aemeasurable (ae_lt_top S.meas_Dinf hfin)]
    rw [hI] at hineq
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    rw [h1 t ht, h1 0 h0, hcongr] at hineq
    exact hineq

end HRS.MC.CepH2
