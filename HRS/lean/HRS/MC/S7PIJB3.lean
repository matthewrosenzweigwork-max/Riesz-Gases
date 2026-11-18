import HRS.MC.S7PIDefs
import HRS.MC.S7PIA

/-!
# Packet piJ (PI-B3): norm convergence of the projected derivatives, `s7_PIB_proj_limit_proof`

The statement of `s7_PIB_proj_limit` (`HRS/MC/S7PIPlan.lean`) copied verbatim.  Route: PI-A
(`HRS.MC.Sec7.PIA.s7_PI_A_heat_derivs_proof`) gives `D^j heatFn γ Φ u (y) = ∫ D^jΦ(y+z) dγ_u(z)`;
the integrands `D^jΦ(P_L(y+z))` converge pointwise in norm to `D^jΦ(y+z)` (continuity of `D^jΦ`
and `P_L w → w`), and are dominated by the constant `⨆ z, ‖D^jΦ z‖` (finite by `MemCb 5 Φ`);
dominated convergence in the normed space of continuous `j`-linear forms.
Namespace `HRS.MC.Sec7.S7PIJ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIJ

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- second countability of the path space (local instance, as in `S7PIA.lean`) -/
local instance s7pij_pathSpace_sc {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- **B3 (removal of the projection in the derivatives: norm convergence)**, proof. -/
theorem s7_PIB_proj_limit_proof {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T))
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 4) (u : ℝ) (y : PathSpace d m T) :
    Tendsto (fun L => projHeatD γ Φ (Pj L) j u y) atTop (𝓝 (iteratedFDeriv ℝ j (heatFn γ Φ u) y)) := by
  have hj5 : j ≤ 5 := by omega
  haveI := hγp u
  have hh : heatFn γ Φ u = heatFn (fun _ => γ u) Φ u := rfl
  have hA : iteratedFDeriv ℝ j (heatFn γ Φ u) y = ∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(γ u) := by
    rw [hh]
    exact ((HRS.MC.Sec7.PIA.s7_PI_A_heat_derivs_proof (γ u) hΦ u).2 j hj5 y).1
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj5)
  rw [hA]
  show Tendsto (fun L => ∫ z, iteratedFDeriv ℝ j Φ (Pj L (y + z)) ∂(γ u)) atTop
    (𝓝 (∫ z, iteratedFDeriv ℝ j Φ (y + z) ∂(γ u)))
  refine tendsto_integral_of_dominated_convergence (F := fun L z => iteratedFDeriv ℝ j Φ (Pj L (y + z)))
    (f := fun z => iteratedFDeriv ℝ j Φ (y + z)) (fun _ => ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) ?_
    (integrable_const _) ?_ ?_
  · intro L
    exact (hcont.comp (by fun_prop : Continuous fun z : PathSpace d m T => Pj L (y + z))).aestronglyMeasurable
  · intro L
    exact Filter.Eventually.of_forall fun z => HRS.MC.Sec7.PIA.pia_le_sup hΦ hj5 (Pj L (y + z))
  · exact Filter.Eventually.of_forall fun z => (hcont.tendsto (y + z)).comp (hconv (y + z))

end HRS.MC.Sec7.S7PIJ

end
