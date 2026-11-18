import HRS.MC.CepP3Aux3

/-!
# Packet P3, Aux4: the space-time measure `ρ` on `ℝ × Config d N` and its periodic lift
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Joint measurability of the progressive process. -/
theorem measurable_joint {ℱ : Filtration ℝ mΩ} {X : ℝ≥0 → Ω → Config d N}
    (hprog : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2) := by
  have hrep : IsProgressive ℱ (fun s ω => repC (ofNNRealTime X s ω)) :=
    isProgressive_comp_measurable' (ofNNRealTime X) hprog (fun _ x => repC x)
      (measurable_repC.comp measurable_snd)
  have hR : Measurable (fun p : ℝ × Ω => repC (ofNNRealTime X p.1 p.2)) :=
    measurable_of_progressive hrep
  have : (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2) =
      fun q => mkC (repC (ofNNRealTime X q.1 q.2)) := by
    funext q
    exact (mk_repC _).symm
  rw [this]
  exact measurable_mkC.comp hR

/-- The space-time measure `ρ = dt ⊗ P_N^t` on `(0,T) × Config`. -/
def rhoM (P : Measure Ω) (T : ℝ) (X : ℝ≥0 → Ω → Config d N) : Measure (ℝ × Config d N) :=
  Measure.map (fun q : ℝ × Ω => (q.1, X (Real.toNNReal q.1) q.2))
    ((volume.restrict (Ioo 0 T)).prod P)

theorem measurable_rhoMap {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2)) :
    Measurable (fun q : ℝ × Ω => (q.1, X (Real.toNNReal q.1) q.2)) :=
  measurable_fst.prodMk hm

theorem isFiniteMeasure_rhoM [IsProbabilityMeasure P] (T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2)) :
    IsFiniteMeasure (rhoM P T X) := by
  unfold rhoM
  have : IsFiniteMeasure (volume.restrict (Ioo 0 T) : Measure ℝ) :=
    ⟨by simp [Real.volume_Ioo]⟩
  exact Measure.isFiniteMeasure_map _ _

theorem rhoM_apply [IsProbabilityMeasure P] (T : ℝ) {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hX : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {S : Set (ℝ × Config d N)} (hS : MeasurableSet S) :
    rhoM P T X S = ∫⁻ t in Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} := by
  unfold rhoM
  rw [Measure.map_apply (measurable_rhoMap hm) hS, Measure.prod_apply (measurable_rhoMap hm hS)]
  refine lintegral_congr fun t => ?_
  have : Prod.mk t ⁻¹' ((fun q : ℝ × Ω => (q.1, X (Real.toNNReal q.1) q.2)) ⁻¹' S) =
      (X (Real.toNNReal t)) ⁻¹' {x | (t, x) ∈ S} := by
    ext ω; simp
  rw [this]
  unfold selectedLaw law
  exact (Measure.map_apply (hX t) (show MeasurableSet {x | (t, x) ∈ S} from
    measurable_prodMk_left hS)).symm

theorem integral_rhoM [IsProbabilityMeasure P] (T : ℝ) {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hX : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {G : ℝ × Config d N → ℝ} (hG : Measurable G) {C : ℝ} (hC : ∀ q, ‖G q‖ ≤ C) :
    ∫ q, G q ∂(rhoM P T X) = ∫ t in Ioo 0 T, ∫ x, G (t, x) ∂(selectedLaw P X t) := by
  unfold rhoM
  rw [integral_map (measurable_rhoMap hm).aemeasurable hG.aestronglyMeasurable]
  have : IsFiniteMeasure (volume.restrict (Ioo 0 T) : Measure ℝ) :=
    ⟨by simp [Real.volume_Ioo]⟩
  have hint : Integrable (fun q : ℝ × Ω => G (q.1, X (Real.toNNReal q.1) q.2))
      ((volume.restrict (Ioo 0 T)).prod P) := by
    refine Integrable.of_bound (C := C) (hG.comp (measurable_rhoMap hm)).aestronglyMeasurable
      (Eventually.of_forall fun q => hC _)
  rw [integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  unfold selectedLaw law
  exact (integral_map (μ := P) (hX t).aemeasurable (f := fun x => G (t, x))
    (hG.comp measurable_prodMk_left).aestronglyMeasurable).symm

end HRS.MC.CepP3
