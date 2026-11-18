import HRS.MC.CepP4Aux1

/-!
# Packet P4, Aux2: the space-time identity `(★)` derived from `hρ`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem star_identity [IsProbabilityMeasure P] {T : ℝ} {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hX : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {f : ℝ → Config d N → ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}))
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))))
    {G : ℝ × Config d N → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, G (t, x) ∂(selectedLaw P X t)
      = ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t, x)) * G (t, x) := by
  classical
  set C := (collisionSet d N)ᶜ with hCdef
  have hCm : MeasurableSet C := (isClosed_collisionSet d N).measurableSet.compl
  set U : Set (ℝ × Config d N) := Ioo 0 T ×ˢ C with hU
  have hUm : MeasurableSet U := measurableSet_Ioo.prod hCm
  have hfh := measurable_fhat hfs
  have hres : (rhoM P T X).restrict U =
      (((volume : Measure ℝ).prod (volume : Measure (Config d N))).restrict U).withDensity
        (fun q => ENNReal.ofReal (fhat f T q)) := by
    refine Measure.ext fun B hB => ?_
    rw [Measure.restrict_apply hB, withDensity_apply _ hB, Measure.restrict_restrict hB]
    rw [rhoM_apply T hm hX (hB.inter hUm), hρ (B ∩ U) (hB.inter hUm) inter_subset_right]
    refine setLIntegral_congr_fun (hB.inter hUm) (fun q hq => ?_)
    rw [fhat_eq hq.2.1 hq.2.2]
  have hGi : Measurable (U.indicator G) := hG.indicator hUm
  have h1 := lintegral_rhoM (P := P) T hm hX hGi
  have h2 : ∫⁻ q, U.indicator G q ∂(rhoM P T X) = ∫⁻ q in U, G q ∂(rhoM P T X) :=
    lintegral_indicator hUm _
  have hmeas : Measurable (fun q : ℝ × Config d N => ENNReal.ofReal (fhat f T q) * G q) :=
    (ENNReal.measurable_ofReal.comp hfh).mul hG
  have h3 : ∫⁻ q in U, G q ∂(rhoM P T X) =
      ∫⁻ q in U, ENNReal.ofReal (fhat f T q) * G q
        ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
    rw [hres, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun q : ℝ × Config d N => ENNReal.ofReal (fhat f T q)) from
        ENNReal.measurable_ofReal.comp hfh) hG]
    rfl
  have h4 : ∫⁻ q in U, ENNReal.ofReal (fhat f T q) * G q
        ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) =
      ∫⁻ t in Ioo 0 T, ∫⁻ x in C, ENNReal.ofReal (fhat f T (t, x)) * G (t, x) := by
    rw [hU, ← Measure.prod_restrict]
    exact lintegral_prod _ hmeas.aemeasurable
  calc ∫⁻ t in Ioo 0 T, ∫⁻ x in C, G (t, x) ∂(selectedLaw P X t)
      = ∫⁻ t in Ioo 0 T, ∫⁻ x, U.indicator G (t, x) ∂(selectedLaw P X t) := by
        refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
        rw [← lintegral_indicator hCm]
        congr 1
        funext x
        by_cases hx : x ∈ C
        · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (show (t, x) ∈ U from ⟨ht, hx⟩)]
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (t, x) ∉ U from fun h => hx h.2)]
    _ = ∫⁻ q, U.indicator G q ∂(rhoM P T X) := h1.symm
    _ = _ := by rw [h2, h3, h4]

end HRS.MC.CepP4
