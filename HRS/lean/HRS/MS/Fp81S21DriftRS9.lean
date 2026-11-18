import HRS.MS.Fp81S21DriftRS8

/-! Almost-everywhere measurability of the exact RS majorant. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21

/-- Continuous sample paths and measurable time sections make the exact
supremum-times-variation expression almost everywhere measurable. -/
theorem fp81s21_rs_bv_variation_majorant_aemeasurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure Ω) (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (q r : ℝ) (hqr : q ≤ r)
    (hA : ∀ t, Measurable (fun ω => ‖A ω t‖))
    (hF : ∀ t, Measurable (fun ω => F ω t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => ‖A ω t‖) (Icc q r) ∧
      ContinuousOn (F ω) (Icc q r)) :
    AEMeasurable (fp81s21_rs_bv_variation_majorant A F q r) μ := by
  classical
  letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
  obtain ⟨s, hs, hsm, hs0⟩ := exists_measurable_superset_of_null (ae_iff.1 hc)
  let g : Ω → ℝ → ℝ := fun ω t => if ω ∈ s then 0 else ‖A ω t‖
  let f : Ω → ℝ → E := fun ω t => if ω ∈ s then 0 else F ω t
  have hgcont : ∀ ω, ContinuousOn (g ω) (Icc q r) := by
    intro ω
    by_cases hω : ω ∈ s
    · simpa [g, hω] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc q r))
    · have hh : ContinuousOn (fun t => ‖A ω t‖) (Icc q r) ∧ ContinuousOn (F ω) (Icc q r) :=
        not_not.mp (fun hn => hω (hs hn))
      simpa [g, hω] using hh.1
  have hfcont : ∀ ω, ContinuousOn (f ω) (Icc q r) := by
    intro ω
    by_cases hω : ω ∈ s
    · simpa [f, hω] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : E)) (Icc q r))
    · have hh : ContinuousOn (fun t => ‖A ω t‖) (Icc q r) ∧ ContinuousOn (F ω) (Icc q r) :=
        not_not.mp (fun hn => hω (hs hn))
      simpa [f, hω] using hh.2
  let G : Ω → C(Icc q r, ℝ) := fun ω => ⟨fun t => g ω t, (hgcont ω).restrict⟩
  let FF : Ω → C(Icc q r, E) := fun ω => ⟨fun t => f ω t, (hfcont ω).restrict⟩
  have hG : Measurable G := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.ite hsm measurable_const (hA t)
  have hFF : Measurable FF := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.ite hsm measurable_const (hF t)
  have hm : AEMeasurable (fun ω => ‖G ω‖ * (eVariationOn (FF ω) univ).toReal) μ :=
    (hG.norm.aemeasurable).mul
      (((fp81s21_continuous_path_variation_measurable (E := E) q r).comp hFF).aemeasurable.ennreal_toReal)
  apply hm.congr
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0] with ω hω
  have hnorm : ‖G ω‖ = ⨆ t : Icc q r, ‖A ω t‖ := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    simp [G, g, hω]
  have hvar : eVariationOn (FF ω) univ = eVariationOn (F ω) (Icc q r) := by
    have hv := eVariationOn.comp_eq_of_monotoneOn (F ω) (t := (univ : Set (Icc q r)))
      (fun t : Icc q r => (t : ℝ)) (fun _ _ _ _ h => h)
    calc
      eVariationOn (FF ω) univ = eVariationOn (fun t : Icc q r => F ω t) univ := by
        apply eVariationOn.congr
        intro t ht
        simp [FF, f, hω]
      _ = eVariationOn (F ω) (Icc q r) := by
        simpa only [Function.comp_def, Set.image_univ, Subtype.range_coe] using hv
  simp [fp81s21_rs_bv_variation_majorant, hnorm, hvar]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_rs_bv_variation_majorant_aemeasurable
