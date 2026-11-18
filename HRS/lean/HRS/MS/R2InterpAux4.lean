import HRS.MS.R2InterpAux3

/-!
# S10.2 (worker S102), part 4: derivatives of the heat function `r2HeatFn` for any probability measure

Whole-space port of the torus packet PI-A (`HRS/MC/S7PIA.lean`): for `Φ ∈ C_b^5(B)` and a probability measure `γ`,
`y ↦ ∫ Φ(y + z) dγ` is `C^5` with `D^j u = ∫ D^jΦ(y + z) dγ` and `‖D^j u‖ ≤ sup‖D^jΦ‖`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

instance s102_oscPath_sc {d : ℕ} {m T : ℝ} : SecondCountableTopology (OscPath d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, OscDual d m))

section Core

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma s102_iter_shift {Φ : B → ℝ} (z : B) (j : ℕ) (x : B) :
    iteratedFDeriv ℝ j (fun y => Φ (y + z)) x = iteratedFDeriv ℝ j Φ (x + z) :=
  iteratedFDeriv_comp_add_right j z x

lemma s102_le_sup {Φ : B → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 5) (y : B) :
    ‖iteratedFDeriv ℝ j Φ y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ :=
  le_ciSup (f := fun z => ‖iteratedFDeriv ℝ j Φ z‖) (hΦ.2 j hj) y

/-- Differentiation under the integral sign for `u(y) = ∫ Φ(y + z) dγ(z)`. -/
theorem s102_heat_derivs [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (γ : Measure B) [IsProbabilityMeasure γ] {Φ : B → ℝ} (hΦ : MemCb 5 Φ) :
    ContDiff ℝ 5 (fun y => ∫ z, Φ (y + z) ∂γ) ∧ ∀ j ≤ 5, ∀ y,
      iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ ∧
      ‖iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ := by
  have hcd : ∀ z : B, ContDiff ℝ ((5 : ℕ) : WithTop ℕ∞) (fun y => Φ (y + z)) := fun z => by
    have := hΦ.1.comp (contDiff_id.add (contDiff_const (c := z)))
    simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := B) γ (fun z y => Φ (y + z)) 5 (by norm_num) hcd
    (fun x => by
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) ?_ ?_
      · exact (hΦ.1.continuous.comp (by fun_prop : Continuous fun z : B => x + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := s102_le_sup hΦ (j := 0) (by norm_num) (x + z)
        simpa using this)
    (fun j hj x => by
      have h : (fun z => iteratedFDeriv ℝ j (fun y => Φ (y + z)) x) =
          fun z => iteratedFDeriv ℝ j Φ (x + z) := by
        funext z; exact s102_iter_shift z j x
      rw [h]
      have := hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj)
      exact (this.comp (by fun_prop : Continuous fun z : B => x + z)).aestronglyMeasurable)
    (fun j _ => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) (fun j _ _ => integrable_const _)
    (fun j _ hj5 z x => by
      rw [s102_iter_shift z j x]; exact s102_le_sup hΦ hj5 _)
  refine ⟨by simpa using key.1, fun j hj y => ?_⟩
  have e := key.2 j hj y
  have e' : iteratedFDeriv ℝ j (fun y => ∫ z, Φ (y + z) ∂γ) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂γ := by
    rw [e]
    congr 1; funext z; exact s102_iter_shift z j y
  refine ⟨e', ?_⟩
  rw [e']
  refine (norm_integral_le_of_norm_le_const (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
    (Filter.Eventually.of_forall fun z => s102_le_sup hΦ hj _)).trans ?_
  simp

end Core

variable {d : ℕ} {m T : ℝ}

/-- `r2HeatFn` for a probability measure `γ_u`: smoothness and the derivative formula. -/
theorem s102_r2HeatFn_derivs (γ : ℝ → Measure (OscPath d m T)) (u : ℝ) [IsProbabilityMeasure (γ u)]
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) :
    ContDiff ℝ 5 (r2HeatFn γ Φ u) ∧ ∀ j ≤ 5, ∀ y,
      iteratedFDeriv ℝ j (r2HeatFn γ Φ u) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(γ u) ∧
      ‖iteratedFDeriv ℝ j (r2HeatFn γ Φ u) y‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖ :=
  s102_heat_derivs (γ u) hΦ

end HRS.MS.R2Interp

end
