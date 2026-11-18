import HRS.Main.GFSpec2

/-!
# Packet GFB3, part 5: a Brownian filtration is a cylindrical Brownian motion (finite subfamilies)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS

lemma gfb3_law_restrict {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' → ι) (he : Function.Injective e)
    (Y : Ω → ι → ℝ) (v : ℝ≥0)
    (h : HasLaw Y (Measure.pi fun _ : ι => gaussianReal 0 v) P) :
    HasLaw (fun ω i => Y ω (e i)) (Measure.pi fun _ : ι' => gaussianReal 0 v) P := by
  classical
  have hY : ∀ i, AEMeasurable (fun ω => Y ω i) P := fun i =>
    (measurable_pi_apply i).comp_aemeasurable h.aemeasurable
  have hmarg : ∀ i, P.map (fun ω => Y ω i) = gaussianReal 0 v := by
    intro i
    have h1 : (fun ω => Y ω i) = (Function.eval i) ∘ Y := rfl
    have h2 := AEMeasurable.map_map_of_aemeasurable (μ := P) (g := Function.eval i) (f := Y)
      (by rw [h.map_eq]; exact (measurable_pi_apply i).aemeasurable) h.aemeasurable
    rw [h1, ← h2, h.map_eq, Measure.pi_map_eval]
    simp
  have hind : iIndepFun (fun i ω => Y ω i) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map hY]
    simp_rw [hmarg]
    exact h.map_eq
  have hind' := hind.precomp he
  have hY' : ∀ i, AEMeasurable (fun ω => Y ω (e i)) P := fun i => hY (e i)
  refine ⟨AEMeasurable.of_eval hY', ?_⟩
  have := (iIndepFun_iff_map_fun_eq_pi_map hY').mp hind'
  rw [this]
  simp_rw [hmarg]

/-- Restriction of a Brownian filtration to a subfamily of the coordinates. -/
theorem gfb3_isBrownianFiltration_restrict {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' → ι) (he : Function.Injective e) {W : ℝ≥0 → Ω → ι → ℝ}
    (hW : IsBrownianFiltration P ℱ W) :
    IsBrownianFiltration P ℱ (fun t ω (i : ι') => W t ω (e i)) where
  complete := hW.complete
  adapted t := by
    letI : MeasurableSpace Ω := ℱ t
    exact measurable_pi_iff.mpr fun i => (measurable_pi_apply (e i)).comp (hW.adapted t)
  zero ω := by
    funext i
    simp [hW.zero ω]
  cont ω := continuous_pi fun i => (continuous_apply (e i)).comp (hW.cont ω)
  indep_incr s t hst := by
    refine indep_of_indep_of_le_left (hW.indep_incr s t hst) ?_
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨(fun x : ι' → ℝ => x) ⁻¹' B |>.preimage (fun y : ι → ℝ => fun i => y (e i)), ?_, ?_⟩
    · exact (measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)) hB
    · rfl
  gaussian_incr s t hst :=
    gfb3_law_restrict e he _ (t - s) (hW.gaussian_incr s t hst)

/-- A Brownian filtration is a cylindrical Brownian motion (every finite subfamily is Brownian). -/
theorem gfb3_isCylindricalBrownian_of_filtration {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {κ : Type*} [Fintype κ] {W : ℝ≥0 → Ω → κ → ℝ}
    (hW : IsBrownianFiltration P ℱ W) : IsCylindricalBrownian P ℱ W := fun s =>
  gfb3_isBrownianFiltration_restrict (fun i : s => (i : κ)) Subtype.val_injective hW

end HRS.GF
