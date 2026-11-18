import HRS.MC.FDLE

/-!
# Packet D3EW, helper 1: differentiation under the integral sign of arbitrary order

Generic lemma: for a family `K t z` jointly smooth on `U × E` (`U ⊆ ℝ` open) with `J ⊆ U` of finite measure
and uniform bounds on all iterated derivatives, the iterated derivatives of `z ↦ ∫_J K t z dt` are the
integrals of the iterated derivatives.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EW

/-- The embedding `z ↦ (0, z)` whose composition computes `fderiv (K t)` from `fderiv (uncurry K)`. -/
def d3ew_L0 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : E →L[ℝ] ℝ × E :=
  (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)

lemma d3ew_fderiv_eq {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set ℝ} (hU : IsOpen U) {K : ℝ → E → F}
    (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ)) {t : ℝ} (ht : t ∈ U) (z : E) :
    fderiv ℝ (K t) z = (fderiv ℝ (Function.uncurry K) (t, z)).comp (d3ew_L0 E) := by
  have hop : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hmem : (t, z) ∈ U ×ˢ (univ : Set E) := ⟨ht, mem_univ _⟩
  have hd : DifferentiableAt ℝ (Function.uncurry K) (t, z) :=
    (hK.differentiableOn (by simp)).differentiableAt (hop.mem_nhds hmem)
  have h1 : HasFDerivAt (fun y : E => ((t, y) : ℝ × E)) (d3ew_L0 E) z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  have h2 := hd.hasFDerivAt.comp z h1
  exact h2.fderiv

lemma d3ew_contDiff_slice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set ℝ} {K : ℝ → E → F}
    (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ)) {t : ℝ} (ht : t ∈ U) :
    ContDiff ℝ ∞ (K t) := by
  have h1 : ContDiff ℝ ∞ (fun y : E => ((t, y) : ℝ × E)) :=
    contDiff_const.prodMk contDiff_id
  rw [← contDiffOn_univ]
  have := hK.comp h1.contDiffOn (s := univ) (fun y _ => ⟨ht, mem_univ _⟩)
  exact this

lemma d3ew_contDiffOn_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set ℝ} (hU : IsOpen U) {K : ℝ → E → F}
    (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t z => fderiv ℝ (K t) z)) (U ×ˢ univ) := by
  have hop : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (Function.uncurry K) p) (U ×ˢ univ) :=
    hK.fderiv_of_isOpen hop (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ (Function.uncurry K) p).comp (d3ew_L0 E))
      (U ×ˢ univ) := h1.clm_comp contDiffOn_const
  refine h2.congr ?_
  rintro ⟨t, z⟩ ⟨ht, -⟩
  exact d3ew_fderiv_eq hU hK ht z

theorem d3ew_hasFDerivAt_integral {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hJfin : volume J < ⊤) (hU : IsOpen U) (hJU : J ⊆ U)
    {K : ℝ → E → F} (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ))
    {B0 B1 : ℝ} (h0 : ∀ t ∈ J, ∀ z, ‖K t z‖ ≤ B0) (h1 : ∀ t ∈ J, ∀ z, ‖fderiv ℝ (K t) z‖ ≤ B1)
    (z0 : E) :
    HasFDerivAt (fun z => ∫ t in J, K t z) (∫ t in J, fderiv ℝ (K t) z0) z0 := by
  have hop : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hcont : ∀ z : E, ContinuousOn (fun t => K t z) J := by
    intro z
    have : ContinuousOn (fun t : ℝ => Function.uncurry K (t, z)) J :=
      hK.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨hJU ht, mem_univ _⟩)
    exact this
  have hcont' : ∀ z : E, ContinuousOn (fun t => fderiv ℝ (K t) z) J := by
    intro z
    have hh := (d3ew_contDiffOn_fderiv hU hK).continuousOn
    have : ContinuousOn (fun t : ℝ => Function.uncurry (fun t z => fderiv ℝ (K t) z) (t, z)) J :=
      hh.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨hJU ht, mem_univ _⟩)
    exact this
  have hfin : (volume.restrict J) univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]; exact hJfin.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict J)
    (F' := fun z t => fderiv ℝ (K t) z) (bound := fun _ => B1) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable hJm) ?_ ?_ ?_ ?_ ?_
  · haveI : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hJfin⟩
    exact Integrable.mono' (integrable_const B0) ((hcont z0).aestronglyMeasurable hJm)
      ((ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht => h0 t ht z0))
  · exact (hcont' z0).aestronglyMeasurable hJm
  · exact (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => h1 t ht z)
  · haveI : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hJfin⟩
    exact integrable_const B1
  · refine (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => ?_)
    exact ((d3ew_contDiff_slice hK (hJU ht)).differentiable (by simp) z).hasFDerivAt

theorem d3ew_iter_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hJfin : volume J < ⊤) (hU : IsOpen U) (hJU : J ⊆ U)
    (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ) →
      (∀ k : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K t) z‖ ≤ B) →
      ∀ z : E, iteratedFDeriv ℝ m (fun z => ∫ t in J, K t z) z
        = ∫ t in J, iteratedFDeriv ℝ m (K t) z := by
  induction m with
  | zero =>
    intro F _ _ _ K hK hB z
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    exact (LinearIsometry.integral_comp_comm
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry (fun t => K t z)).symm
  | succ m ih =>
    intro F _ _ _ K hK hB z
    set K' : ℝ → E → (E →L[ℝ] F) := fun t z => fderiv ℝ (K t) z with hK'
    have hK'd : ContDiffOn ℝ ∞ (Function.uncurry K') (U ×ˢ univ) := d3ew_contDiffOn_fderiv hU hK
    have hB' : ∀ k : ℕ, ∃ B : ℝ, ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K' t) z‖ ≤ B := by
      intro k
      obtain ⟨B, hB⟩ := hB (k + 1)
      refine ⟨B, fun t ht z => ?_⟩
      show ‖iteratedFDeriv ℝ k (fderiv ℝ (K t)) z‖ ≤ B
      rw [norm_iteratedFDeriv_fderiv]
      exact hB t ht z
    obtain ⟨B0, hB0⟩ := hB 0
    obtain ⟨B1, hB1⟩ := hB 1
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, K' t z := by
      funext y
      refine HasFDerivAt.fderiv (d3ew_hasFDerivAt_integral hJm hJfin hU hJU hK (B0 := B0) (B1 := B1)
        (fun t ht z => ?_) (fun t ht z => ?_) y)
      · simpa using hB0 t ht z
      · have := hB1 t ht z
        rwa [norm_iteratedFDeriv_one] at this
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    rw [hder, ih K' hK'd hB' z]
    have key := LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := volume.restrict J)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin m => E) (E →L[ℝ] F))
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F)
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.toLinearIsometry
      (fun t => iteratedFDeriv ℝ m (K' t) z)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
    rfl

end HRS.MC.D3EW
