import HRS.MS.S113TransitionAux1

/-!
# S11.3.K2 (breakdown packet K2): signed `L¹` contraction for differences under a substochastic density kernel
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S113BD

variable {α : Type*} [MeasurableSpace α]

theorem s113_transition_L1 (lam : Measure α) [SFinite lam]
    (k : α → α → ℝ) (hk : Measurable (Function.uncurry k))
    (hk0 : ∀ x y, 0 ≤ k x y)
    (hki : ∀ x, Integrable (k x) lam)
    (hkm : ∀ x, ∫ y, k x y ∂lam ≤ 1)
    (f g : α → ℝ) (hf : Integrable f lam) (hg : Integrable g lam) :
    (∫ y, |(∫ x, k x y * f x ∂lam) - (∫ x, k x y * g x ∂lam)| ∂lam) ≤
      ∫ x, |f x - g x| ∂lam := by
  have hfg : Integrable (fun x => f x - g x) lam := hf.sub hg
  obtain ⟨-, h2, -⟩ := s113_transition_duality lam k hk hk0 hki hkm (fun x => f x - g x) hfg
  have hFf := s113_kf_integrable lam k hk hk0 hki hkm f hf
  have hFg := s113_kf_integrable lam k hk hk0 hki hkm g hg
  have hae : ∀ᵐ y ∂lam, (∫ x, k x y * f x ∂lam) - (∫ x, k x y * g x ∂lam) =
      ∫ x, k x y * (f x - g x) ∂lam := by
    filter_upwards [hFf.prod_left_ae, hFg.prod_left_ae] with y h1 h2
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  calc ∫ y, |(∫ x, k x y * f x ∂lam) - (∫ x, k x y * g x ∂lam)| ∂lam
      = ∫ y, |∫ x, k x y * (f x - g x) ∂lam| ∂lam :=
        integral_congr_ae (hae.mono fun y hy => congrArg abs hy)
    _ ≤ _ := h2

end HRS.MS.S113BD
