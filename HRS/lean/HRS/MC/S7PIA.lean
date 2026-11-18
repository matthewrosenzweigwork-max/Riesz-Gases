import HRS.MC.Sec7Vocab

/-!
# Packet PI-A: derivatives of the heat function for any probability measure

`s7_PI_A_heat_derivs_proof`: differentiation under the integral sign for `u(y) = ∫ Φ(y + z) dγ(z)`
on `PathSpace d m T`, via `HRS.contDiff_integral_dominated`.  Namespace `HRS.MC.Sec7.PIA`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIA

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- second countability of the path space (local instance; avoids importing the packages that add it globally) -/
local instance pia_pathSpace_sc {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

section Core

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma pia_iter_shift {Φ : B → ℝ} (z : B) (j : ℕ) (x : B) :
    iteratedFDeriv ℝ j (fun y => Φ (y + z)) x = iteratedFDeriv ℝ j Φ (x + z) :=
  iteratedFDeriv_comp_add_right j z x

lemma pia_le_sup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 5) (y : B) :
    ‖iteratedFDeriv ℝ j Φ y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ :=
  le_ciSup (f := fun z => ‖iteratedFDeriv ℝ j Φ z‖) (hΦ.2 j hj) y

end Core

theorem s7_PI_A_heat_derivs_proof {m T : ℝ} (γ : Measure (PathSpace d m T)) [IsProbabilityMeasure γ]
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (u : ℝ) :
    ContDiff ℝ 5 (heatFn (fun _ => γ) Φ u) ∧ ∀ j ≤ 5, ∀ y,
      iteratedFDeriv ℝ j (heatFn (fun _ => γ) Φ u) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ ∧
      ‖iteratedFDeriv ℝ j (heatFn (fun _ => γ) Φ u) y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := by
  have hfun : heatFn (fun _ => γ) Φ u = fun y => ∫ z, (fun z y => Φ (y + z)) z y ∂γ := rfl
  have hcd : ∀ z : PathSpace d m T, ContDiff ℝ ((5 : ℕ) : WithTop ℕ∞) (fun y => Φ (y + z)) := fun z => by
    have := hΦ.1.comp (contDiff_id.add (contDiff_const (c := z)))
    simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := PathSpace d m T) γ (fun z y => Φ (y + z)) 5 (by norm_num) hcd
    (fun x => by
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) ?_ ?_
      · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun z : PathSpace d m T => x + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := pia_le_sup hΦ (j := 0) (by norm_num) (x + z)
        simpa using this)
    (fun j hj x => by
      have h : (fun z => iteratedFDeriv ℝ j (fun y => Φ (y + z)) x) =
          fun z => iteratedFDeriv ℝ j Φ (x + z) := by
        funext z; exact pia_iter_shift z j x
      rw [h]
      have := hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
      exact (this.comp (by fun_prop : Continuous fun z : PathSpace d m T => x + z)).aestronglyMeasurable)
    (fun j _ => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) (fun j _ _ => integrable_const _)
    (fun j _ hj5 z x => by
      rw [pia_iter_shift z j x]; exact pia_le_sup hΦ hj5 _)
  refine ⟨by rw [hfun]; simpa using key.1, fun j hj y => ?_⟩
  have e := key.2 j hj y
  have e' : iteratedFDeriv ℝ j (heatFn (fun _ => γ) Φ u) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ := by
    rw [hfun, e]
    congr 1; funext z; exact pia_iter_shift z j y
  refine ⟨e', ?_⟩
  rw [e']
  refine (norm_integral_le_of_norm_le_const (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
    (Filter.Eventually.of_forall fun z => pia_le_sup hΦ hj _)).trans ?_
  simp

end HRS.MC.Sec7.PIA
