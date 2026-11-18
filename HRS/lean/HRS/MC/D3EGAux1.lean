import HRS.MC.D3EW

/-!
# Packet D3EG, helper 1: differentiation under the integral sign with integrable (non-constant) bounds

Variant of `HRS.MC.D3EW.d3ew_iter_integral` for an arbitrary measurable index set `J` (possibly of infinite
measure): the derivative bounds are integrable functions `B t` and only the iterated derivatives of order `≥ 1`
need bounds (plus integrability of `t ↦ K t z`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EG

open HRS.MC.D3EW

/-- Hypotheses on a family `K t z`. -/
def d3eg_Hyp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (J U : Set ℝ) (K : ℝ → E → F) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ) ∧ (∀ z, IntegrableOn (fun t => K t z) J) ∧
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ → ℝ, IntegrableOn B J ∧
    ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K t) z‖ ≤ B t

lemma d3eg_cont_slice {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J U : Set ℝ} (hJU : J ⊆ U) {K : ℝ → E → F}
    (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ)) (z : E) :
    ContinuousOn (fun t => K t z) J := by
  have : ContinuousOn (fun t : ℝ => Function.uncurry K (t, z)) J :=
    hK.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hJU ht, mem_univ _⟩)
  exact this

theorem d3eg_hasFDerivAt_integral {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U)
    {K : ℝ → E → F} (h : d3eg_Hyp J U K) (z0 : E) :
    HasFDerivAt (fun z => ∫ t in J, K t z) (∫ t in J, fderiv ℝ (K t) z0) z0 := by
  obtain ⟨hK, hint, hB⟩ := h
  obtain ⟨B1, hB1int, hB1⟩ := hB 1 le_rfl
  have hcont : ∀ z : E, ContinuousOn (fun t => K t z) J := d3eg_cont_slice hJU hK
  have hcont' : ∀ z : E, ContinuousOn (fun t => fderiv ℝ (K t) z) J := by
    intro z
    have hh := (d3ew_contDiffOn_fderiv hU hK).continuousOn
    have : ContinuousOn (fun t : ℝ => Function.uncurry (fun t z => fderiv ℝ (K t) z) (t, z)) J :=
      hh.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨hJU ht, mem_univ _⟩)
    exact this
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict J)
    (F' := fun z t => fderiv ℝ (K t) z) (bound := B1) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable hJm) (hint z0) ?_ ?_ hB1int ?_
  · exact (hcont' z0).aestronglyMeasurable hJm
  · refine (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => ?_)
    have := hB1 t ht z
    rwa [norm_iteratedFDeriv_one] at this
  · refine (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => ?_)
    exact ((d3ew_contDiff_slice hK (hJU ht)).differentiable (by simp) z).hasFDerivAt

/-- The hypotheses pass to the derivative family. -/
lemma d3eg_Hyp_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U)
    (hJU : J ⊆ U) {K : ℝ → E → F} (h : d3eg_Hyp J U K) :
    d3eg_Hyp J U (fun t z => fderiv ℝ (K t) z) := by
  obtain ⟨hK, hint, hB⟩ := h
  have hK' := d3ew_contDiffOn_fderiv hU hK
  refine ⟨hK', ?_, ?_⟩
  · intro z
    obtain ⟨B1, hB1int, hB1⟩ := hB 1 le_rfl
    have hcont' : ContinuousOn (fun t => fderiv ℝ (K t) z) J := by
      have hh := hK'.continuousOn
      have : ContinuousOn (fun t : ℝ => Function.uncurry (fun t z => fderiv ℝ (K t) z) (t, z)) J :=
        hh.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun t ht => ⟨hJU ht, mem_univ _⟩)
      exact this
    refine Integrable.mono' hB1int (hcont'.aestronglyMeasurable hJm) ?_
    refine (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have := hB1 t ht z
    rwa [norm_iteratedFDeriv_one] at this
  · intro k hk
    obtain ⟨B, hBint, hBb⟩ := hB (k + 1) (by omega)
    refine ⟨B, hBint, fun t ht z => ?_⟩
    show ‖iteratedFDeriv ℝ k (fderiv ℝ (K t)) z‖ ≤ B t
    rw [norm_iteratedFDeriv_fderiv]
    exact hBb t ht z

theorem d3eg_iter_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U) (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      d3eg_Hyp J U K →
      ∀ z : E, iteratedFDeriv ℝ m (fun z => ∫ t in J, K t z) z
        = ∫ t in J, iteratedFDeriv ℝ m (K t) z := by
  induction m with
  | zero =>
    intro F _ _ _ K hK z
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    exact (LinearIsometry.integral_comp_comm
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry (fun t => K t z)).symm
  | succ m ih =>
    intro F _ _ _ K hK z
    set K' : ℝ → E → (E →L[ℝ] F) := fun t z => fderiv ℝ (K t) z with hK'
    have hK'd : d3eg_Hyp J U K' := d3eg_Hyp_fderiv hJm hU hJU hK
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, K' t z := by
      funext y
      exact (d3eg_hasFDerivAt_integral hJm hU hJU hK y).fderiv
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    rw [hder, ih K' hK'd z]
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

theorem d3eg_contDiff_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      d3eg_Hyp J U K → ContDiff ℝ n (fun z => ∫ t in J, K t z) := by
  induction n with
  | zero =>
    intro F _ _ _ K hK
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y =>
      (d3eg_hasFDerivAt_integral hJm hU hJU hK y).continuousAt
  | succ n ih =>
    intro F _ _ _ K hK
    have hK'd : d3eg_Hyp J U (fun t z => fderiv ℝ (K t) z) := d3eg_Hyp_fderiv hJm hU hJU hK
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, fderiv ℝ (K t) z := by
      funext y
      exact (d3eg_hasFDerivAt_integral hJm hU hJU hK y).fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun y => (d3eg_hasFDerivAt_integral hJm hU hJU hK y).differentiableAt, by simp, ?_⟩
    rw [hder]
    exact ih _ hK'd

end HRS.MC.D3EG
