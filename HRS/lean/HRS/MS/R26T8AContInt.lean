import HRS.MS.R26T8APot1
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# S8.2 nonlocal layer: smoothness of a parametric integral on an open set (P11e, part 3b tool)
`r26t8a_contDiffOn_integral`: under the hypotheses of `r26t8a_iter_integral` (`G s` of class `C^k` on the open set `U`, integrable majorant `Phi` of
`‖D^i (G s)‖`, `i <= k`), `y ↦ ∫ G s y` is `C^k` on `U`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_contDiffOn_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (G : Ω → E → F) (k : ℕ) (hG : ∀ᵐ s ∂μ, ∀ x ∈ U, ContDiffAt ℝ (k : WithTop ℕ∞) (G s) x)
    {Φ : Ω → ℝ} (hΦ : Integrable Φ μ)
    (hbd : ∀ i ≤ k, ∀ᵐ s ∂μ, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (G s) x‖ ≤ Φ s)
    (hmeas : ∀ i ≤ k, ∀ x ∈ U, AEStronglyMeasurable (fun s => iteratedFDeriv ℝ i (G s) x) μ) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (fun y => ∫ s, G s y ∂μ) U := by
  have hform := r26t8a_iter_integral hU G k hG hΦ hbd hmeas
  have e1 : ∀ (i : ℕ) (s : Ω) (y : E), fderiv ℝ (iteratedFDeriv ℝ i (G s)) y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F
        (iteratedFDeriv ℝ (i + 1) (G s) y) := by
    intro i s y
    rw [iteratedFDeriv_succ_eq_comp_left]; simp
  have step : ∀ i < k, ∀ x ∈ U, HasFDerivAt (fun y => ∫ s, iteratedFDeriv ℝ i (G s) y ∂μ)
      (∫ s, fderiv ℝ (iteratedFDeriv ℝ i (G s)) x ∂μ) x := by
    intro i hi x hx
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y s => iteratedFDeriv ℝ i (G s) y)
      (F' := fun y s => fderiv ℝ (iteratedFDeriv ℝ i (G s)) y) (s := U) (bound := Φ)
      (hU.mem_nhds hx) ?_ ?_ ?_ ?_ hΦ ?_
    · filter_upwards [hU.mem_nhds hx] with y hy using hmeas i hi.le y hy
    · exact hΦ.mono' (hmeas i hi.le x hx) ((hbd i hi.le).mono fun s h => h x hx)
    · have e : (fun s => fderiv ℝ (iteratedFDeriv ℝ i (G s)) x) = fun s =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F
            (iteratedFDeriv ℝ (i + 1) (G s) x) := funext fun s => e1 i s x
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).continuous.comp_aestronglyMeasurable
        (hmeas (i + 1) hi x hx)
    · filter_upwards [hbd (i + 1) hi] with s h y hy
      rw [e1, LinearIsometryEquiv.norm_map]; exact h y hy
    · filter_upwards [hG] with s h y hy
      exact ((h y hy).differentiableAt_iteratedFDeriv (by exact_mod_cast hi)).hasFDerivAt
  have eq : ∀ m ≤ k, Set.EqOn (iteratedFDerivWithin ℝ m (fun y => ∫ s, G s y ∂μ) U)
      (fun x => ∫ s, iteratedFDeriv ℝ m (G s) x ∂μ) U := fun m hm x hx => by
    rw [iteratedFDerivWithin_of_isOpen m hU hx]; exact hform m hm x hx
  have hmain : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun y => ∫ s, G s y ∂μ) U := by
    refine contDiffOn_of_continuousOn_differentiableOn (n := (k : ℕ∞)) (fun m hm => ?_) (fun m hm => ?_)
    · have hmk : m ≤ k := by exact_mod_cast hm
      have hc : ContinuousOn (fun x => ∫ s, iteratedFDeriv ℝ m (G s) x ∂μ) U :=
        continuousOn_of_dominated (bound := Φ) (fun x hx => hmeas m hmk x hx)
          (fun x hx => (hbd m hmk).mono fun s h => h x hx) hΦ
          (by
            filter_upwards [hG] with s h
            have hon : ContDiffOn ℝ (k : WithTop ℕ∞) (G s) U := fun x hx => (h x hx).contDiffWithinAt
            exact ContinuousOn.continuousOn_iteratedFDeriv hon hU (by exact_mod_cast hmk))
      exact hc.congr (eq m hmk)
    · have hmk : m < k := by exact_mod_cast hm
      have hd : DifferentiableOn ℝ (fun x => ∫ s, iteratedFDeriv ℝ m (G s) x ∂μ) U :=
        fun x hx => (step m hmk x hx).differentiableAt.differentiableWithinAt
      exact hd.congr (eq m hmk.le)
  exact_mod_cast hmain

end HRS.MS.R26T8A
