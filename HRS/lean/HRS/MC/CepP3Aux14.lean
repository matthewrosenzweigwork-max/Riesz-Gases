import HRS.MC.CepP3Aux13

/-!
# Packet P3, Aux14: the parabolic Weyl lemma on the covering space `ℝ × (Fin N → Euc d)`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

theorem weyl_cov {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O)
    {b : ℝ × (Fin N → Euc d) → Fin N → Euc d} (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O)
    {invβ : ℝ} (hβ : 0 < invβ) {ρ : Measure (ℝ × (Fin N → Euc d))}
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (heq : ∀ F : ℝ × (Fin N → Euc d) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F → HasCompactSupport F →
        tsupport F ⊆ O → ∫ p, Lop invβ b F p ∂ρ = 0) :
    ∃ f : ℝ × (Fin N → Euc d) → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O ∧ (∀ p ∈ O, 0 ≤ f p) ∧
      ρ.restrict O = (volume.restrict O).withDensity (fun p => ENNReal.ofReal (f p)) := by
  classical
  set A := Acl d N with hA
  have hAm : MeasurableEmbedding A := A.toHomeomorph.measurableEmbedding
  have hAsm : MeasurableEmbedding A.symm := A.symm.toHomeomorph.measurableEmbedding
  set O' := A ⁻¹' O with hO'def
  have hO' : IsOpen O' := hO.preimage A.continuous
  set b' : ℝ × EuclideanSpace ℝ (Fin (N * d)) → EuclideanSpace ℝ (Fin (N * d)) :=
    fun q => (Jc d N).symm (b (A q)) with hb'def
  have hb' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b' O' :=
    (Jc d N).symm.contDiff.comp_contDiffOn (hb.comp A.contDiff.contDiffOn (fun q hq => hq))
  set ρ' := Measure.map A.symm ρ with hρ'def
  have hρ' : ∀ K, K ⊆ O' → IsCompact K → ρ' K < ⊤ := by
    intro K hKO hK
    rw [hρ'def, hAsm.map_apply]
    have : A.symm ⁻¹' K = A '' K := by
      ext x
      exact ⟨fun h => ⟨A.symm x, h, A.apply_symm_apply x⟩, by rintro ⟨y, hy, rfl⟩; simpa using hy⟩
    rw [this]
    exact hρ _ (by rintro _ ⟨y, hy, rfl⟩; exact hKO hy) (hK.image A.continuous)
  have heq' : ∀ Φ : ℝ × EuclideanSpace ℝ (Fin (N * d)) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ O' →
      ∫ p, (fderiv ℝ Φ p (1, 0)
              + invβ * ∑ k : Fin (N * d), fderiv ℝ (fderiv ℝ Φ) p (0, EuclideanSpace.single k 1)
                  (0, EuclideanSpace.single k 1)
              + fderiv ℝ Φ p (0, b' p)) ∂ρ' = 0 := by
    intro Φ hΦ hc hts
    set F : ℝ × (Fin N → Euc d) → ℝ := fun q => Φ (A.symm q) with hF
    have hΦF : Φ = fun q => F (A q) := by funext q; simp [hF]
    have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hΦ.comp A.symm.contDiff
    have hFc : HasCompactSupport F := hc.comp_homeomorph A.symm.toHomeomorph
    have hFt : tsupport F ⊆ O := by
      have : tsupport F = A.symm ⁻¹' tsupport Φ := by
        unfold tsupport
        rw [show F = Φ ∘ A.symm from rfl, Function.support_comp_eq_preimage]
        exact (A.symm.toHomeomorph.preimage_closure _).symm
      rw [this]
      intro q hq
      have := hts hq
      simpa [hO'def] using this
    have key := heq F hFs hFc hFt
    rw [hρ'def, hAsm.integral_map]
    refine Eq.trans ?_ key
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have h := Lp2_comp invβ b (F := F) (hFs.of_le two_le_infty) (A.symm q)
    rw [hA, ContinuousLinearEquiv.apply_symm_apply] at h
    rw [hΦF]
    exact h
  obtain ⟨f', hf'sm, hf'nn, hf'eq⟩ := HRS.MC.CepP2.cep_P2_parabolic_weyl_proof hO' hb' hβ hρ' heq'
  obtain ⟨c, hc, hcmap⟩ := map_Acl_volume (d := d) (N := N)
  rw [← hA] at hcmap
  have hmaps : ∀ p ∈ O, A.symm p ∈ O' := fun p hp => by
    show A (A.symm p) ∈ O
    rw [A.apply_symm_apply]; exact hp
  set f'm : ℝ × EuclideanSpace ℝ (Fin (N * d)) → ℝ := O'.indicator f' with hf'm
  have hf'mm : Measurable f'm := by
    have h1 : ContinuousOn f' O' := hf'sm.continuousOn
    have := h1.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hO'.measurableSet
    convert this using 1
    funext x
    by_cases hx : x ∈ O' <;> simp [hf'm, hx]
  have hf'm_eq : ∀ x ∈ O', f'm x = f' x := fun x hx => Set.indicator_of_mem hx _
  have hh : Measurable fun p : ℝ × (Fin N → Euc d) => ENNReal.ofReal (f'm (A.symm p)) :=
    ENNReal.measurable_ofReal.comp (hf'mm.comp A.symm.continuous.measurable)
  refine ⟨fun p => c * f'm (A.symm p), ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => c * f' (A.symm p)) O :=
      contDiffOn_const.mul (hf'sm.comp A.symm.contDiff.contDiffOn hmaps)
    exact h1.congr fun p hp => by
      show c * f'm (A.symm p) = c * f' (A.symm p)
      rw [hf'm_eq _ (hmaps p hp)]
  · intro p hp
    show 0 ≤ c * f'm (A.symm p)
    rw [hf'm_eq _ (hmaps p hp)]
    exact mul_nonneg hc.le (hf'nn _ (hmaps p hp))
  · refine Measure.ext fun B hB => ?_
    have hρρ : ∀ S, MeasurableSet S → ρ' (A ⁻¹' S) = ρ S := by
      intro S hS
      rw [hρ'def, hAsm.map_apply]
      congr 1
      ext x; simp
    rw [Measure.restrict_apply hB, withDensity_apply _ hB, Measure.restrict_restrict hB]
    have hA1 : ρ (B ∩ O) = ∫⁻ x in A ⁻¹' B, ENNReal.ofReal (f' x) ∂(volume.restrict O') := by
      rw [← hρρ _ (hB.inter hO.measurableSet)]
      have e1 : A ⁻¹' (B ∩ O) = A ⁻¹' B ∩ O' := rfl
      rw [e1, ← Measure.restrict_apply (A.continuous.measurable hB), hf'eq,
        withDensity_apply _ (A.continuous.measurable hB)]
    rw [hA1, Measure.restrict_restrict (A.continuous.measurable hB)]
    have e2 : ∫⁻ p, ENNReal.ofReal (c * f'm (A.symm p)) ∂(volume.restrict (B ∩ O))
        = ∫⁻ p, ENNReal.ofReal c * ENNReal.ofReal (f'm (A.symm p)) ∂(volume.restrict (B ∩ O)) :=
      lintegral_congr fun p => ENNReal.ofReal_mul hc.le
    have e3 : (Measure.map A volume).restrict (B ∩ O) = ENNReal.ofReal c • volume.restrict (B ∩ O) := by
      rw [hcmap, Measure.restrict_smul]
    have e4 : ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (f'm (A.symm p)) ∂(volume.restrict (B ∩ O))
        = ∫⁻ p, ENNReal.ofReal (f'm (A.symm p)) ∂((Measure.map A volume).restrict (B ∩ O)) := by
      rw [e3, lintegral_smul_measure]; rfl
    rw [e2, lintegral_const_mul _ hh, e4, Measure.restrict_map hAm.measurable (hB.inter hO.measurableSet),
      hAm.lintegral_map]
    have hmeasS : MeasurableSet (A ⁻¹' B ∩ O') := (A.continuous.measurable hB).inter hO'.measurableSet
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hmeasS] with x hx
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    rw [hf'm_eq x hx.2]

end HRS.MC.CepP3
