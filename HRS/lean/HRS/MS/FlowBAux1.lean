import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# MS-FLOW-B, measurability in time of the `x`-derivatives of the drift

`b` is only continuous in `τ`; the derivatives `D^j b(τ, x)` are limits of difference quotients, hence
strongly measurable in `τ` for fixed `x`; along a continuous path `ζ` the maps `τ ↦ D^j b(τ, ζ τ)` are
strongly measurable (Carathéodory).
-/

open MeasureTheory Filter Topology

namespace HRS.MS.FlowB

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- Directional derivatives are strongly measurable in the parameter. -/
theorem sm_fderiv_apply (u : ℝ → E → W) (hd : ∀ s, Differentiable ℝ (u s))
    (hm : ∀ y, StronglyMeasurable (fun s => u s y)) (y v : E) :
    StronglyMeasurable (fun s => fderiv ℝ (u s) y v) := by
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun (n : ℕ) s => ((n : ℝ) + 1) • (u s (y + (1 / ((n : ℝ) + 1)) • v) - u s y))
    (fun n => ?_) ?_
  · exact ((hm _).sub (hm y)).const_smul _
  · rw [tendsto_pi_nhds]
    intro s
    have h2 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
    have h1 : HasDerivAt (fun t : ℝ => u s (y + t • v)) (fderiv ℝ (u s) y v) 0 := by
      have h3 : HasFDerivAt (u s) (fderiv ℝ (u s) y) (y + (0 : ℝ) • v) := by
        simpa using (hd s y).hasFDerivAt
      exact h3.comp_hasDerivAt (0 : ℝ) h2
    have h4 := h1.tendsto_slope_zero
    have h5 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Eventually.of_forall fun n => by simp; positivity
    refine (h4.comp h5).congr fun n => ?_
    simp

/-- The derivative is strongly measurable in the parameter. -/
theorem sm_fderiv [FiniteDimensional ℝ E] (u : ℝ → E → W) (hd : ∀ s, Differentiable ℝ (u s))
    (hm : ∀ y, StronglyMeasurable (fun s => u s y)) (y : E) :
    StronglyMeasurable (fun s => fderiv ℝ (u s) y) := by
  classical
  let bs := Module.finBasis ℝ E
  have key : ∀ s, fderiv ℝ (u s) y = ∑ i, (ContinuousLinearMap.smulRightL ℝ E W
      (LinearMap.toContinuousLinearMap (bs.coord i))) (fderiv ℝ (u s) y (bs i)) := by
    intro s
    ext v
    conv_lhs => rw [← bs.sum_repr v, map_sum]
    simp only [map_smul]
    simp
  have : (fun s => fderiv ℝ (u s) y) = fun s => ∑ i, (ContinuousLinearMap.smulRightL ℝ E W
      (LinearMap.toContinuousLinearMap (bs.coord i))) (fderiv ℝ (u s) y (bs i)) :=
    funext key
  rw [this]
  refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact (ContinuousLinearMap.continuous _).comp_stronglyMeasurable
    (sm_fderiv_apply u hd hm y (bs i))

/-- Iterated derivatives are strongly measurable in the parameter. -/
theorem sm_iteratedFDeriv [FiniteDimensional ℝ E] (f : ℝ → E → W) {n : WithTop ℕ∞}
    (hf : ∀ s, ContDiff ℝ n (f s)) (hm : ∀ y, StronglyMeasurable (fun s => f s y)) :
    ∀ j : ℕ, (j : WithTop ℕ∞) ≤ n → ∀ y, StronglyMeasurable (fun s => iteratedFDeriv ℝ j (f s) y) := by
  intro j
  induction j with
  | zero =>
    intro _ y
    have : (fun s => iteratedFDeriv ℝ 0 (f s) y) =
        fun s => (continuousMultilinearCurryFin0 ℝ E W).symm (f s y) := by
      funext s; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (LinearIsometryEquiv.continuous _).comp_stronglyMeasurable (hm y)
  | succ j ih =>
    intro hj y
    have hjn : (j : WithTop ℕ∞) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) hj
    have hd : ∀ s, Differentiable ℝ (iteratedFDeriv ℝ j (f s)) := fun s =>
      (hf s).differentiable_iteratedFDeriv hjn
    have h1 := sm_fderiv (fun s => iteratedFDeriv ℝ j (f s)) hd
      (ih ((Nat.cast_le.2 (Nat.le_succ j)).trans hj)) y
    have : (fun s => iteratedFDeriv ℝ (j + 1) (f s) y) = fun s =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) W).symm
          (fderiv ℝ (iteratedFDeriv ℝ j (f s)) y) := by
      funext s; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [this]
    exact (LinearIsometryEquiv.continuous _).comp_stronglyMeasurable h1

/-- Carathéodory: along a continuous path. -/
theorem sm_comp_path [FiniteDimensional ℝ E] (Ψ : ℝ → E → W) (hc : ∀ s, Continuous (Ψ s))
    (hm : ∀ y, StronglyMeasurable (fun s => Ψ s y)) {ζ : ℝ → E} (hζ : Continuous ζ) :
    StronglyMeasurable (fun s => Ψ s (ζ s)) := by
  borelize E
  have h := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun (y : E) (s : ℝ) => Ψ s y) (fun s => hc s) (fun y => hm y)
  exact h.comp_measurable (hζ.measurable.prodMk measurable_id)

end HRS.MS.FlowB
