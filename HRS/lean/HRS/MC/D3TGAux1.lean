import HRS.MC.D3EWAux2
import HRS.MC.D3T1Aux1
import HRS.MC.Per

/-!
# Packet D3TG, helper 1: differentiation under the integral sign over a possibly infinite interval

Generalisation of `HRS.MC.D3EW.d3ew_iter_integral`: the uniform bounds are replaced by integrable majorants,
so that `J` may have infinite measure.  Also: smoothness of `z ↦ ∫_J K t z dt`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS.MC.D3EW

theorem d3tg_hasFDerivAt_integral {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U)
    {K : ℝ → E → F} (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ))
    {ρ0 ρ1 : ℝ → ℝ} (hρ0 : IntegrableOn ρ0 J) (hρ1 : IntegrableOn ρ1 J)
    (h0 : ∀ t ∈ J, ∀ z, ‖K t z‖ ≤ ρ0 t) (h1 : ∀ t ∈ J, ∀ z, ‖fderiv ℝ (K t) z‖ ≤ ρ1 t)
    (z0 : E) :
    HasFDerivAt (fun z => ∫ t in J, K t z) (∫ t in J, fderiv ℝ (K t) z0) z0 := by
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
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict J)
    (F' := fun z t => fderiv ℝ (K t) z) (bound := ρ1) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable hJm) ?_ ?_ ?_ ?_ ?_
  · exact Integrable.mono' hρ0 ((hcont z0).aestronglyMeasurable hJm)
      ((ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht => h0 t ht z0))
  · exact (hcont' z0).aestronglyMeasurable hJm
  · exact (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => h1 t ht z)
  · exact hρ1
  · refine (ae_restrict_iff' hJm).2 (Filter.Eventually.of_forall fun t ht z _ => ?_)
    exact ((d3ew_contDiff_slice hK (hJU ht)).differentiable (by simp) z).hasFDerivAt

/-- The package of hypotheses: integrable majorants of all iterated derivatives. -/
def D3TGBound {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (J : Set ℝ) (K : ℝ → E → F) : Prop :=
  ∀ k : ℕ, ∃ ρ : ℝ → ℝ, IntegrableOn ρ J ∧ ∀ t ∈ J, ∀ z, ‖iteratedFDeriv ℝ k (K t) z‖ ≤ ρ t

lemma d3tg_bound_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {J : Set ℝ} {K : ℝ → E → F} (hB : D3TGBound J K) :
    D3TGBound J (fun t z => fderiv ℝ (K t) z) := by
  intro k
  obtain ⟨ρ, hρ, hb⟩ := hB (k + 1)
  refine ⟨ρ, hρ, fun t ht z => ?_⟩
  show ‖iteratedFDeriv ℝ k (fderiv ℝ (K t)) z‖ ≤ ρ t
  rw [norm_iteratedFDeriv_fderiv]
  exact hb t ht z

theorem d3tg_fderiv_integral {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U)
    {K : ℝ → E → F} (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ))
    (hB : D3TGBound J K) (z : E) :
    HasFDerivAt (fun z => ∫ t in J, K t z) (∫ t in J, fderiv ℝ (K t) z) z := by
  obtain ⟨ρ0, hρ0, hb0⟩ := hB 0
  obtain ⟨ρ1, hρ1, hb1⟩ := hB 1
  refine d3tg_hasFDerivAt_integral hJm hU hJU hK hρ0 hρ1 (fun t ht w => ?_) (fun t ht w => ?_) z
  · simpa using hb0 t ht w
  · have := hb1 t ht w
    rwa [norm_iteratedFDeriv_one] at this

theorem d3tg_iter_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U) (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ) → D3TGBound J K →
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
    have hB' : D3TGBound J K' := d3tg_bound_fderiv hB
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, K' t z := by
      funext y
      exact (d3tg_fderiv_integral hJm hU hJU hK hB y).fderiv
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

theorem d3tg_contDiff_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U) (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : ℝ → E → F),
      ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ) → D3TGBound J K →
      ContDiff ℝ m (fun z => ∫ t in J, K t z) := by
  induction m with
  | zero =>
    intro F _ _ _ K hK hB
    rw [Nat.cast_zero, contDiff_zero]
    exact Differentiable.continuous (fun z => (d3tg_fderiv_integral hJm hU hJU hK hB z).differentiableAt)
  | succ m ih =>
    intro F _ _ _ K hK hB
    have hdiff : Differentiable ℝ (fun z => ∫ t in J, K t z) :=
      fun z => (d3tg_fderiv_integral hJm hU hJU hK hB z).differentiableAt
    set K' : ℝ → E → (E →L[ℝ] F) := fun t z => fderiv ℝ (K t) z with hK'
    have hK'd : ContDiffOn ℝ ∞ (Function.uncurry K') (U ×ˢ univ) := d3ew_contDiffOn_fderiv hU hK
    have hder : fderiv ℝ (fun z => ∫ t in J, K t z) = fun z => ∫ t in J, K' t z := by
      funext y
      exact (d3tg_fderiv_integral hJm hU hJU hK hB y).fderiv
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨hdiff, by simp, ?_⟩
    rw [hder]
    exact ih K' hK'd (d3tg_bound_fderiv hB)

theorem d3tg_contDiff_integral_infty {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {J U : Set ℝ} (hJm : MeasurableSet J) (hU : IsOpen U) (hJU : J ⊆ U)
    (K : ℝ → E → F) (hK : ContDiffOn ℝ ∞ (Function.uncurry K) (U ×ˢ univ)) (hB : D3TGBound J K) :
    ContDiff ℝ ∞ (fun z => ∫ t in J, K t z) := by
  rw [contDiff_infty]
  exact fun m => d3tg_contDiff_integral hJm hU hJU m K hK hB

end HRS.MC.D3TG
