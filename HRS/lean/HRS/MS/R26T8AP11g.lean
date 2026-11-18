import HRS.MS.R26T8AP11g13
import HRS.MS.R26T8AP11g7
import HRS.MS.R26T8AP11g5

/-!
# S8.2 T8A P11g: `r26t8a_nonlocal_rows` (Pro contract, verbatim)
(a) the row identity: `r26t8a_g5_row`; (b) the jets of the `x`-averaged row: `r26t8a_g7_jets` (row lemma);
(c) the canonical row: `r26t8a_g13_canon_row`.  The constant is uniform in `ρ` because the thermal density is unique.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_nonlocal_rows (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Q : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (k + 2) b M (sigma - 2) A Q →
      let Jx := fun x y => oneJ (critCoeff d a beta rho) (fun u => Q u y) x
      (∀ y, Integrable (fun x => Jx x y) (HRS.Whole.withDensityReal rho) ∧
        ∫ x, Jx x y ∂HRS.Whole.withDensityReal rho =
          -∫ u, inner ℝ (forceMean rho u) (pairGradX Q u y) ∂HRS.Whole.withDensityReal rho) ∧
      (∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j
        (fun z => ∫ x, Jx x z ∂HRS.Whole.withDensityReal rho) y‖ ≤ C * A * jbracket y ^ (M + 2)) ∧
      (CanonicalPair (HRS.Whole.withDensityReal rho) Q →
        ∀ x, Integrable (Jx x) (HRS.Whole.withDensityReal rho) ∧
          ∫ y, Jx x y ∂HRS.Whole.withDensityReal rho = 0) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  obtain ⟨C, hC0, hC⟩ := r26t8a_g7_jets d hd k b a beta M sigma ha hbeta hM hsd h0
  refine ⟨C, hC0, ?_⟩
  intro rho hrho Q A hA hQ Jx
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  refine ⟨fun y => r26t8a_g5_row d hd k b a beta M sigma ha hbeta hM hsd rho hrho Q A hA hQ y,
    fun j hj y => hC Q A hA hQ j hj y, fun hcan x => ?_⟩
  have hcan' : ∀ u, ∫ y, rho y * Q u y = 0 := fun u => by
    rw [← r26t8a_f25_wd_integral hprob (Q u)]
    exact hcan.2.2.2 u
  obtain ⟨hI, hz⟩ := r26t8a_g13_canon_row d hd k b a beta M sigma ha hbeta hM hsd hrho hA hQ hcan' x
  refine ⟨(r26t8a_f25_wd_integrable hprob (Jx x)).2 hI, ?_⟩
  rw [r26t8a_f25_wd_integral hprob]
  exact hz

end HRS.MS.R26T8A
