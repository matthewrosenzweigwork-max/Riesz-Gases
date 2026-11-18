import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# S8.2 nonlocal layer: iterated differentiation under the integral sign on an open set
`r26t8a_iter_integral`: if every `G w` is `C^k` on an open set `U`, with an integrable majorant of
`D^i (G w)` on `U` for `i <= k`, then `D^i (fun y => int G w y) = int D^i (G w)` on `U`, `i <= k`.
This is the local version of `HRS.MS.Lc.lc4_iteratedFDeriv_integral` (no global bound in `x`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_iter_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    (G : Ω → E → F) (k : ℕ) (hG : ∀ᵐ s ∂μ, ∀ x ∈ U, ContDiffAt ℝ (k : WithTop ℕ∞) (G s) x)
    {Φ : Ω → ℝ} (hΦ : Integrable Φ μ)
    (hbd : ∀ i ≤ k, ∀ᵐ s ∂μ, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (G s) x‖ ≤ Φ s)
    (hmeas : ∀ i ≤ k, ∀ x ∈ U, AEStronglyMeasurable (fun s => iteratedFDeriv ℝ i (G s) x) μ) :
    ∀ i ≤ k, ∀ x ∈ U, iteratedFDeriv ℝ i (fun y => ∫ s, G s y ∂μ) x =
      ∫ s, iteratedFDeriv ℝ i (G s) x ∂μ := by
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
  intro i
  induction i with
  | zero =>
    intro _ x _
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp]
    have : ∀ s, iteratedFDeriv ℝ 0 (G s) x =
        (continuousMultilinearCurryFin0 ℝ E F).symm (G s x) := fun s => by
      rw [iteratedFDeriv_zero_eq_comp]; rfl
    simp_rw [this]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ i ih =>
    intro hi x hx
    have hev : iteratedFDeriv ℝ i (fun y => ∫ s, G s y ∂μ) =ᶠ[𝓝 x]
        fun y => ∫ s, iteratedFDeriv ℝ i (G s) y ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih (Nat.le_of_succ_le hi) y hy
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp, hev.fderiv_eq, (step i hi x hx).fderiv]
    have : ∀ s, iteratedFDeriv ℝ (i + 1) (G s) x =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm
          (fderiv ℝ (iteratedFDeriv ℝ i (G s)) x) := fun s => by
      rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    simp_rw [this]
    simpa using (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
      (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => E) F) (μ := μ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm.toLinearIsometry
      (fun s => fderiv ℝ (iteratedFDeriv ℝ i (G s)) x)).symm

end HRS.MS.R26T8A
