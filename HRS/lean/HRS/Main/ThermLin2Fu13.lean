import HRS.Main.ThermLin2Dy5
import HRS.Main.ThermLin2Fu12

/-!
# THERMLIN2 Fu13: the weak Dyson identity `Tl2FuTest.hweak` from `tl2_dyson_pairing` and the dual evolutions

**Uses the plan statement `tl2_dyson_pairing` (B1) as a black box**; the orchestrator swaps in
`tl2_dyson_pairing_proof` (wk/tl2dyson, Dy5) at integration.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

/-- The weak Dyson identity: `⟨Vev z, φ⟩ - ⟨Wev z, φ⟩ = ∫_σ^t ⟨Wev(r,σ) z, Δ_r U^{r,t}φ⟩ dr`.  (Uses the plan
statement `tl2_dyson_pairing`.) -/
theorem tl2fu_hweak_core (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVd : IsDualEvolution S.dyn S.ρ m Vev) (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t σ : ℝ} (hσ : 0 ≤ σ) (hσt : σ ≤ t)
    (hsm : σ < t → ∀ r ∈ Set.Icc σ t, Torus.IsSmooth (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)))
    (z : NegSobolev d m) :
    NegSobolev.eval (Vev t σ z) φ - NegSobolev.eval (Wev t σ z) φ =
      ∫ r in σ..t, NegSobolev.eval (Wev r σ z) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := by
  have hB1 := tl2_dyson_pairing_proof S h m hm hφ hσ hσt z
  rw [hVd σ t hσ hσt z φ hφ, hWd σ t hσ hσt z φ hφ]
  have e : ∫ r in σ..t, NegSobolev.eval (Wev r σ z) (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) =
      ∫ r in σ..t, NegSobolev.eval z (tl2Ub S ρβ σ r (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))) := by
    rcases hσt.eq_or_lt with heq | hlt
    · subst heq; simp
    · refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le hσt] at hr
      exact hWd σ r hσ hr.1 z _ (hsm hlt r hr)
  rw [e, hB1]
  show _ - NegSobolev.eval z (propagator S.dyn (fun _ => ρβ) σ t φ) = _
  ring

end HRS.ThermLin.Plan2
